import Leader.AAFJ.Centered.Sanitation

/-!
# Deterministic local route for centered one-barrier cleanup

This module is intentionally one cohesive file.  It records the finite-word
machinery and the source-exact local facts used by the repaired linear cleanup
route.  The global endpoint-sterile sweep is built from the two-hit facts below;
it is not allowed to assume that a parked barrier makes both endpoints globally
mark-free.
-/

namespace AAFJPK
namespace CenteredRenewal
namespace OneBarrierCleanup

open BarrierAlgebra
open SingleBarrierSanitation

set_option autoImplicit false

/-- The packaged centered configuration step, named locally to keep finite-word
statements readable. -/
def step {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (e : Fin n) : Fin n → State k :=
  (CenteredRenewal.protocol k hk).step ring C e

/-- Execute a finite word of directed edges, from left to right. -/
def runWord {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) : List (Fin n) → Fin n → State k
  | [] => C
  | e :: w => runWord hk ring (step hk ring C e) w

@[simp] theorem runWord_nil {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) : runWord hk ring C [] = C := rfl

@[simp] theorem runWord_cons {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (e : Fin n) (w : List (Fin n)) :
    runWord hk ring C (e :: w) = runWord hk ring (step hk ring C e) w := rfl

theorem runWord_append {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (u v : List (Fin n)) :
    runWord hk ring C (u ++ v) = runWord hk ring (runWord hk ring C u) v := by
  induction u generalizing C with
  | nil => simp
  | cons e u ih => simp [runWord, ih]

/-- A word whose every edge avoids a vertex leaves that vertex literally
unchanged.  This is the common frame rule for the two directional sweeps. -/
theorem runWord_frame {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (w : List (Fin n)) (i : Fin n)
    (havoid : ∀ e ∈ w, i ≠ e ∧ i ≠ ring.rightNeighbor e) :
    runWord hk ring C w i = C i := by
  induction w generalizing C with
  | nil => rfl
  | cons e w ih =>
      have he := havoid e (by simp)
      have hw : ∀ f ∈ w, i ≠ f ∧ i ≠ ring.rightNeighbor f := by
        intro f hf
        exact havoid f (by simp [hf])
      rw [runWord_cons, ih (step hk ring C e) hw]
      simp [step, PopulationProtocol.step, he.1, he.2]

/-- The two consecutive interactions used by each repaired sweep edge. -/
def doubleHit {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (e : Fin n) : Fin n → State k :=
  runWord hk ring C [e, e]

@[simp] theorem doubleHit_eq {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (e : Fin n) :
    doubleHit hk ring C e = step hk ring (step hk ring C e) e := rfl

/-! ## The parked sweep word -/

/-- Duplicate every selected edge.  The literal ordinary transition needs the
second hit when the first hit only kills a bullet-carrying leader responder. -/
def duplicateEdges {α : Type} : List α → List α
  | [] => []
  | e :: w => e :: e :: duplicateEdges w

@[simp] theorem duplicateEdges_nil {α : Type} :
    duplicateEdges ([] : List α) = [] := rfl

@[simp] theorem duplicateEdges_cons {α : Type} (e : α) (w : List α) :
    duplicateEdges (e :: w) = e :: e :: duplicateEdges w := rfl

theorem duplicateEdges_length {α : Type} (w : List α) :
    (duplicateEdges w).length = 2 * w.length := by
  induction w with
  | nil => simp
  | cons e w ih => simp [ih, Nat.mul_add]

@[simp] theorem mem_duplicateEdges_iff {α : Type} (x : α) (w : List α) :
    x ∈ duplicateEdges w ↔ x ∈ w := by
  induction w with
  | nil => simp
  | cons e w ih => simp [ih]

/-- Embed a non-tail cut coordinate into the full ring coordinate type. -/
def pathCoord {n : Nat} (ring : DirectedRing n) (i : Fin (n - 1)) : Fin n :=
  ⟨i.val, by have := i.isLt; have := ring.hn; omega⟩

@[simp] theorem pathCoord_val {n : Nat} (ring : DirectedRing n)
    (i : Fin (n - 1)) : (pathCoord ring i).val = i.val := rfl

/-- The ordinary cut edges, from the barrier head toward its tail.  The last
cut coordinate is omitted because its outgoing edge is the unique barrier. -/
def cutPathEdges {n : Nat} (ring : DirectedRing n) (b : Fin n) : List (Fin n) :=
  (List.finRange (n - 1)).map (fun i => cutPos ring b (pathCoord ring i))

theorem cutPathEdges_length {n : Nat} (ring : DirectedRing n) (b : Fin n) :
    (cutPathEdges ring b).length = n - 1 := by
  simp [cutPathEdges]

/-- Every listed path edge is ordinary relative to the parked barrier. -/
theorem mem_cutPathEdges_ne_barrier {n : Nat} (ring : DirectedRing n)
    (b e : Fin n) (he : e ∈ cutPathEdges ring b) : e ≠ b := by
  rw [cutPathEdges, List.mem_map] at he
  obtain ⟨i, hi, rfl⟩ := he
  intro hib
  have hitail : pathCoord ring i = tailCoord ring := by
    apply cutPos_injective ring b
    simpa using hib
  have hiLt := i.isLt
  have hval := congrArg Fin.val hitail
  change i.val = n - 1 at hval
  omega

/-- In the forward list, an earlier initiator is neither endpoint of any later
edge. -/
theorem cutPathEdges_pairwise_forward {n : Nat} (ring : DirectedRing n)
    (b : Fin n) :
    (cutPathEdges ring b).Pairwise
      (fun e f => e ≠ f ∧ e ≠ ring.rightNeighbor f) := by
  unfold cutPathEdges
  apply (List.pairwise_lt_finRange (n - 1)).map
  intro i j hij
  constructor
  · intro heq
    have hc : pathCoord ring i = pathCoord ring j :=
      cutPos_injective ring b heq
    have hv := congrArg Fin.val hc
    exact (Nat.ne_of_lt hij) (by simpa using hv)
  · rw [← cutPos_rightNeighbor]
    intro heq
    have hc : pathCoord ring i = ring.rightNeighbor (pathCoord ring j) :=
      cutPos_injective ring b heq
    have hjne : pathCoord ring j ≠ tailCoord ring := by
      intro htail
      have hv := congrArg Fin.val htail
      change j.val = n - 1 at hv
      have hjlt := j.isLt
      omega
    have hr := rightNeighbor_val_of_ne_tail ring (pathCoord ring j) hjne
    have hcval := congrArg Fin.val hc
    change i.val = (ring.rightNeighbor (pathCoord ring j)).val at hcval
    change (ring.rightNeighbor (pathCoord ring j)).val = j.val + 1 at hr
    omega

/-- In the reversed path, an earlier responder is neither endpoint of a later
edge. -/
theorem cutPathEdges_reverse_pairwise {n : Nat} (ring : DirectedRing n)
    (b : Fin n) :
    (cutPathEdges ring b).reverse.Pairwise (fun e f =>
      ring.rightNeighbor e ≠ f ∧
        ring.rightNeighbor e ≠ ring.rightNeighbor f) := by
  rw [List.pairwise_reverse]
  unfold cutPathEdges
  apply (List.pairwise_lt_finRange (n - 1)).map
  intro i j hij
  have hjne : pathCoord ring j ≠ tailCoord ring := by
    intro htail
    have hv := congrArg Fin.val htail
    change j.val = n - 1 at hv
    have hjlt := j.isLt
    omega
  constructor
  · rw [← cutPos_rightNeighbor]
    intro heq
    have hc : ring.rightNeighbor (pathCoord ring j) = pathCoord ring i :=
      cutPos_injective ring b heq
    have hr := rightNeighbor_val_of_ne_tail ring (pathCoord ring j) hjne
    have hcval := congrArg Fin.val hc
    change (ring.rightNeighbor (pathCoord ring j)).val = i.val at hcval
    change (ring.rightNeighbor (pathCoord ring j)).val = j.val + 1 at hr
    omega
  · intro heq
    have hbase : cutPos ring b (pathCoord ring j) =
        cutPos ring b (pathCoord ring i) :=
      rightNeighbor_injective ring heq
    have hc : pathCoord ring j = pathCoord ring i :=
      cutPos_injective ring b hbase
    have hcval := congrArg Fin.val hc
    change j.val = i.val at hcval
    omega

/-- Conversely, every physical edge other than the parked barrier occurs in
the cut path exactly where its cut coordinate says it should. -/
theorem mem_cutPathEdges_of_ne_barrier {n : Nat} (ring : DirectedRing n)
    (b e : Fin n) (he : e ≠ b) : e ∈ cutPathEdges ring b := by
  let c := cutCoord ring b e
  have hcne : c ≠ tailCoord ring := by
    intro htail
    apply he
    have htail' : cutCoord ring b e = tailCoord ring := by
      simpa [c] using htail
    rw [← cutPos_cutCoord ring b e, htail', cutPos_tailCoord]
  have hcval : c.val ≠ n - 1 := by
    intro hv
    apply hcne
    apply Fin.ext
    exact hv
  have hclt : c.val < n - 1 := by
    have hcLtN := c.isLt
    omega
  let i : Fin (n - 1) := ⟨c.val, hclt⟩
  rw [cutPathEdges, List.mem_map]
  refine ⟨i, List.mem_finRange i, ?_⟩
  have hic : pathCoord ring i = c := by
    apply Fin.ext
    rfl
  rw [hic, cutPos_cutCoord]

theorem mem_cutPathEdges_leftNeighbor_of_ne_head {n : Nat}
    (ring : DirectedRing n) (b i : Fin n)
    (hi : i ≠ ring.rightNeighbor b) :
    ring.leftNeighbor i ∈ cutPathEdges ring b := by
  apply mem_cutPathEdges_of_ne_barrier ring b
  intro hleft
  apply hi
  rw [← rightNeighbor_leftNeighbor_clean ring i, hleft]

/-- Forward doubled hits clear probes; reverse doubled hits clear bullets. -/
def parkedSweepWord {n : Nat} (ring : DirectedRing n) (b : Fin n) :
    List (Fin n) :=
  let path := cutPathEdges ring b
  duplicateEdges path ++ duplicateEdges path.reverse

theorem parkedSweepWord_length {n : Nat} (ring : DirectedRing n) (b : Fin n) :
    (parkedSweepWord ring b).length = 4 * (n - 1) := by
  simp [parkedSweepWord, duplicateEdges_length, cutPathEdges_length]
  omega

/-- Executing a duplicated prefix exposes one `doubleHit`, which is the
induction step used by both sweep directions. -/
theorem runWord_duplicateEdges_cons {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (e : Fin n)
    (w : List (Fin n)) :
    runWord hk ring C (duplicateEdges (e :: w)) =
      runWord hk ring (doubleHit hk ring C e) (duplicateEdges w) := by
  rfl

theorem runWord_duplicateEdges_frame {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (w : List (Fin n))
    (i : Fin n) (havoid : ∀ e ∈ w, i ≠ e ∧ i ≠ ring.rightNeighbor e) :
    runWord hk ring C (duplicateEdges w) i = C i := by
  apply runWord_frame hk ring C (duplicateEdges w) i
  intro e he
  exact havoid e ((mem_duplicateEdges_iff e w).1 he)

/-! ## Existing centered barrier transport -/

/-- Re-export the actual centered one-barrier transport theorem under the
cleanup namespace.  It is label/charge exact, not merely a barrier-count bound. -/
theorem oneBarrier_step {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b e : Fin n)
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b) :
    OneBarrierAt hk ring (step hk ring C e)
      (if CenteredRenewal.AdvanceReady hk ring C e then
        ring.rightNeighbor b else b) := by
  exact CenteredRenewal.Sanitation.oneBarrierAt_step hk ring hn2 C b e hndvd hone

/-- A genuine centered advance sanitizes the responder, which is the new
barrier tail.  No head-probe side condition is present in this variant. -/
theorem advance_sanitizes_new_tail {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n)
    (hone : OneBarrierAt hk ring C b)
    (hphase : (C b).phase = true) :
    ((step hk ring C b) (ring.rightNeighbor b)).phase = false ∧
      ((step hk ring C b) (ring.rightNeighbor b)).bullet = false ∧
      ((step hk ring C b) (ring.rightNeighbor b)).probe = false := by
  have hbar : IsBarrier hk (C b) (C (ring.rightNeighbor b)) :=
    (barrierAt_labelsOf_iff hk ring C b).mp ((hone b).2 rfl)
  have hpair := CenteredRenewal.barrierStep_phase_one hk
    (C b) (C (ring.rightNeighbor b)) hphase
  have htrans : CenteredRenewal.transition hk (C b) (C (ring.rightNeighbor b)) =
      (probeHitsBarrier (C b),
        { C (ring.rightNeighbor b) with
          label := succLabel hk (C b).label
          phase := false
          bullet := false
          probe := false }) := by
    rw [CenteredRenewal.transition_of_barrier hk _ _ hbar]
    exact hpair
  have hre : ring.rightNeighbor b ≠ b := rightNeighbor_ne_self ring hn2 b
  simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans, hre]

/-! ## Literal ordinary branch -/

/-- An ordinary centered transition never creates a leader.  Its initiator
leader bit is unchanged; a leader responder may disappear but cannot be born. -/
theorem nonbarrier_transition_no_leader_birth {k : Nat} (hk : 0 < k)
    (u v : State k) (hbar : ¬ IsBarrier hk u v) :
    (CenteredRenewal.transition hk u v).1.leader = u.leader ∧
      ((CenteredRenewal.transition hk u v).2.leader = true → v.leader = true) := by
  rw [CenteredRenewal.transition_of_nonbarrier hk u v hbar]
  cases hv : v.leader <;> cases hb : v.bullet <;> cases hp : u.probe <;>
    simp [nonBarrierStep, hv, hb, hp]

/-- If an ordinary-edge initiator has no probe, that interaction preserves the
probe field at both endpoints. -/
theorem nonbarrier_transition_probes_of_initiator_clear {k : Nat}
    (hk : 0 < k) (u v : State k) (hbar : ¬ IsBarrier hk u v)
    (hu : u.probe = false) :
    (CenteredRenewal.transition hk u v).1.probe = false ∧
      (CenteredRenewal.transition hk u v).2.probe = v.probe := by
  rw [CenteredRenewal.transition_of_nonbarrier hk u v hbar]
  cases hv : v.leader <;> cases hb : v.bullet <;>
    simp [nonBarrierStep, hv, hb, hu]

/-- Global form of ordinary no-birth for the packaged centered step. -/
theorem step_no_leader_birth_of_nonbarrier {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e))) :
    ∀ i : Fin n, ((step hk ring C e) i).leader = true → (C i).leader = true := by
  intro i hi
  have hlocal := nonbarrier_transition_no_leader_birth hk
    (C e) (C (ring.rightNeighbor e)) hbar
  have hre : ring.rightNeighbor e ≠ e := rightNeighbor_ne_self ring hn2 e
  by_cases hie : i = e
  · subst i
    have hleft : (CenteredRenewal.transition hk (C e)
        (C (ring.rightNeighbor e))).1.leader = true := by
      simpa [step, PopulationProtocol.step, CenteredRenewal.protocol, hre] using hi
    rw [hlocal.1] at hleft
    exact hleft
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      have hright : (CenteredRenewal.transition hk (C e)
          (C (ring.rightNeighbor e))).2.leader = true := by
        simpa [step, PopulationProtocol.step, CenteredRenewal.protocol, hre, hie] using hi
      exact hlocal.2 hright
    · simpa [step, PopulationProtocol.step, CenteredRenewal.protocol, hie, hir] using hi

theorem step_probes_eq_of_nonbarrier_initiator_clear {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)))
    (hprobe : (C e).probe = false) :
    ∀ i : Fin n, (step hk ring C e i).probe = (C i).probe := by
  have hlocal := nonbarrier_transition_probes_of_initiator_clear hk
    (C e) (C (ring.rightNeighbor e)) hbar hprobe
  have hre : ring.rightNeighbor e ≠ e := rightNeighbor_ne_self ring hn2 e
  intro i
  by_cases hie : i = e
  · subst i
    simpa [step, PopulationProtocol.step, CenteredRenewal.protocol, hprobe]
      using hlocal.1
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      simpa [step, PopulationProtocol.step, CenteredRenewal.protocol, hre, hie]
        using hlocal.2
    · simp [step, PopulationProtocol.step, CenteredRenewal.protocol, hie, hir]

/-- Two local ordinary hits clear the initiator probe, including the case where
the first hit only kills a bullet-carrying leader responder. -/
theorem nonbarrier_double_probe_clear {k : Nat} (u v : State k) :
    (nonBarrierStep (nonBarrierStep u v).1 (nonBarrierStep u v).2).1.probe = false := by
  cases hv : v.leader <;> cases hb : v.bullet <;> cases hp : u.probe <;>
    simp [nonBarrierStep, hv, hb, hp]

/-- Two local ordinary hits clear the responder bullet.  If it was carried by
a leader, the first hit removes that leader and the second performs the usual
follower bullet move. -/
theorem nonbarrier_double_responder_bullet_clear {k : Nat} (u v : State k) :
    (nonBarrierStep (nonBarrierStep u v).1 (nonBarrierStep u v).2).2.bullet = false := by
  cases hv : v.leader <;> cases hb : v.bullet <;> cases hp : u.probe <;>
    simp [nonBarrierStep, hv, hb, hp]

/-- Source-order corridor engine: if the responder carries a bullet, two
ordinary hits leave a probe-free bullet at the initiator and turn the responder
into a bullet-free follower. -/
theorem nonbarrier_double_bullet_progress {k : Nat} (u v : State k)
    (hbullet : v.bullet = true) :
    let z := nonBarrierStep (nonBarrierStep u v).1 (nonBarrierStep u v).2
    z.1.bullet = true ∧ z.1.probe = false ∧
      z.2.bullet = false ∧ z.2.leader = false := by
  cases hv : v.leader <;> cases hp : u.probe <;>
    simp [nonBarrierStep, hv, hbullet, hp]

/-- A nonbarrier centered step has no label effect, so the selected edge stays
ordinary when selected a second time. -/
theorem labels_step_eq_self_of_nonbarrier {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (e : Fin n)
    (hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e))) :
    labelsOf (step hk ring C e) = labelsOf C := by
  apply CenteredRenewal.labelsOf_step_eq_self_of_not_ready hk ring C e
  intro hready
  exact hbar hready.1

theorem nonbarrier_after_step {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (e : Fin n)
    (hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e))) :
    ¬ IsBarrier hk ((step hk ring C e) e)
      ((step hk ring C e) (ring.rightNeighbor e)) := by
  intro hbarD
  have hlabels := labels_step_eq_self_of_nonbarrier hk ring C e hbar
  have hD : BarrierAt hk ring (labelsOf (step hk ring C e)) e :=
    (barrierAt_labelsOf_iff hk ring (step hk ring C e) e).2 hbarD
  rw [hlabels] at hD
  exact hbar ((barrierAt_labelsOf_iff hk ring C e).1 hD)

/-- A doubled ordinary hit preserves every probe bit when its initiator starts
probe-free. -/
theorem doubleHit_probes_eq_of_nonbarrier_initiator_clear {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)))
    (hprobe : (C e).probe = false) :
    ∀ i : Fin n, (doubleHit hk ring C e i).probe = (C i).probe := by
  let C1 := step hk ring C e
  have hfirst := step_probes_eq_of_nonbarrier_initiator_clear hk ring hn2
    C e hbar hprobe
  have hbar1 : ¬ IsBarrier hk (C1 e) (C1 (ring.rightNeighbor e)) := by
    simpa [C1] using nonbarrier_after_step hk ring C e hbar
  have hprobe1 : (C1 e).probe = false := by
    rw [hfirst e, hprobe]
  have hsecond := step_probes_eq_of_nonbarrier_initiator_clear hk ring hn2
    C1 e hbar1 hprobe1
  intro i
  change (step hk ring C1 e i).probe = (C i).probe
  rw [hsecond i, hfirst i]

/-- The actual two-edge word has exactly the iterated local ordinary pair
transition.  This is the bridge from source-order truth tables to a parked
sweep over a physical ring edge. -/
theorem doubleHit_pair_of_nonbarrier {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e))) :
    (doubleHit hk ring C e e,
      doubleHit hk ring C e (ring.rightNeighbor e)) =
      nonBarrierStep
        (nonBarrierStep (C e) (C (ring.rightNeighbor e))).1
        (nonBarrierStep (C e) (C (ring.rightNeighbor e))).2 := by
  let C1 := step hk ring C e
  have hre : ring.rightNeighbor e ≠ e := rightNeighbor_ne_self ring hn2 e
  have her : e ≠ ring.rightNeighbor e := Ne.symm hre
  have htrans : CenteredRenewal.transition hk (C e) (C (ring.rightNeighbor e)) =
      nonBarrierStep (C e) (C (ring.rightNeighbor e)) := by
    exact CenteredRenewal.transition_of_nonbarrier hk _ _ hbar
  have hleft : C1 e = (nonBarrierStep (C e) (C (ring.rightNeighbor e))).1 := by
    simp [C1, step, PopulationProtocol.step, CenteredRenewal.protocol, htrans]
  have hright : C1 (ring.rightNeighbor e) =
      (nonBarrierStep (C e) (C (ring.rightNeighbor e))).2 := by
    simp [C1, step, PopulationProtocol.step, CenteredRenewal.protocol, htrans, hre]
  have hbar1 : ¬ IsBarrier hk (C1 e) (C1 (ring.rightNeighbor e)) := by
    simpa [C1] using nonbarrier_after_step hk ring C e hbar
  have htrans1 : CenteredRenewal.transition hk (C1 e)
      (C1 (ring.rightNeighbor e)) =
      nonBarrierStep
        (nonBarrierStep (C e) (C (ring.rightNeighbor e))).1
        (nonBarrierStep (C e) (C (ring.rightNeighbor e))).2 := by
    rw [CenteredRenewal.transition_of_nonbarrier hk _ _ hbar1, hleft, hright]
  apply Prod.ext
  · change step hk ring C1 e e = _
    have hsecond : step hk ring C1 e e =
        (CenteredRenewal.transition hk (C1 e)
          (C1 (ring.rightNeighbor e))).1 := by
      simp [step, PopulationProtocol.step, CenteredRenewal.protocol]
    exact hsecond.trans (congrArg Prod.fst htrans1)
  · change step hk ring C1 e (ring.rightNeighbor e) = _
    have hsecond : step hk ring C1 e (ring.rightNeighbor e) =
        (CenteredRenewal.transition hk (C1 e)
          (C1 (ring.rightNeighbor e))).2 := by
      simp [step, PopulationProtocol.step, CenteredRenewal.protocol, hre]
    exact hsecond.trans (congrArg Prod.snd htrans1)

/-- The two-hit physical sanitizer clears the initiator probe. -/
theorem doubleHit_probe_clear_of_nonbarrier {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e))) :
    (doubleHit hk ring C e e).probe = false := by
  have hpair := doubleHit_pair_of_nonbarrier hk ring hn2 C e hbar
  have hlocal := nonbarrier_double_probe_clear (C e) (C (ring.rightNeighbor e))
  have hfirst := congrArg (fun p : State k × State k => p.1.probe) hpair
  exact hfirst.trans hlocal

/-- The two-hit physical bullet move clears the responder.  Any old bullet
there has progressed counterclockwise to the initiator or was absent. -/
theorem doubleHit_responder_bullet_clear_of_nonbarrier {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e))) :
    (doubleHit hk ring C e (ring.rightNeighbor e)).bullet = false := by
  have hpair := doubleHit_pair_of_nonbarrier hk ring hn2 C e hbar
  have hlocal := nonbarrier_double_responder_bullet_clear
    (C e) (C (ring.rightNeighbor e))
  have hsecond := congrArg (fun p : State k × State k => p.2.bullet) hpair
  exact hsecond.trans hlocal

/-- Configuration-level corridor engine corresponding to
`nonbarrier_double_bullet_progress`. -/
theorem doubleHit_bullet_progress_of_nonbarrier {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)))
    (hbullet : (C (ring.rightNeighbor e)).bullet = true) :
    (doubleHit hk ring C e e).bullet = true ∧
      (doubleHit hk ring C e e).probe = false ∧
      (doubleHit hk ring C e (ring.rightNeighbor e)).bullet = false ∧
      (doubleHit hk ring C e (ring.rightNeighbor e)).leader = false := by
  have hpair := doubleHit_pair_of_nonbarrier hk ring hn2 C e hbar
  have hlocal := nonbarrier_double_bullet_progress
    (C e) (C (ring.rightNeighbor e)) hbullet
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (congrArg (fun p : State k × State k => p.1.bullet) hpair).trans
      hlocal.1
  · exact (congrArg (fun p : State k × State k => p.1.probe) hpair).trans
      hlocal.2.1
  · exact (congrArg (fun p : State k × State k => p.2.bullet) hpair).trans
      hlocal.2.2.1
  · exact (congrArg (fun p : State k × State k => p.2.leader) hpair).trans
      hlocal.2.2.2

/-- A doubled hit frames all vertices other than the selected edge endpoints. -/
theorem doubleHit_frame {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    doubleHit hk ring C e i = C i := by
  simp [doubleHit, runWord, step, PopulationProtocol.step, hi, hj]

/-- Two hits of a presently ordinary edge still cannot create a leader. -/
theorem doubleHit_no_leader_birth_of_nonbarrier {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e))) :
    ∀ i : Fin n, (doubleHit hk ring C e i).leader = true → (C i).leader = true := by
  let C1 := step hk ring C e
  have hbar1 : ¬ IsBarrier hk (C1 e) (C1 (ring.rightNeighbor e)) := by
    simpa [C1] using nonbarrier_after_step hk ring C e hbar
  have hfirst := step_no_leader_birth_of_nonbarrier hk ring hn2 C e hbar
  have hsecond := step_no_leader_birth_of_nonbarrier hk ring hn2 C1 e hbar1
  intro i hi
  apply hfirst i
  apply hsecond i
  simpa [doubleHit, C1] using hi

/-! ## Parked barrier interface -/

/-- The repaired sweep invariant: probes may remain only at the barrier tail,
and bullets may remain only at the barrier head.  This deliberately does not
duplicate or strengthen the repository's `Clean` predicate. -/
def EndpointSterile {n k : Nat} (ring : DirectedRing n)
    (C : Fin n → State k) (b : Fin n) : Prop :=
  (∀ i : Fin n, i ≠ b → (C i).probe = false) ∧
    ∀ i : Fin n, i ≠ ring.rightNeighbor b → (C i).bullet = false

/-- A doubled ordinary interaction leaves the unique barrier at its old
physical edge.  This is the parked-barrier unit used by both sweep directions. -/
theorem doubleHit_parks_unique_barrier {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b e : Fin n)
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b) (he : e ≠ b) :
    OneBarrierAt hk ring (doubleHit hk ring C e) b := by
  have hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
    intro h
    apply he
    apply (hone e).1
    exact (barrierAt_labelsOf_iff hk ring C e).2 h
  have hnot : ¬ CenteredRenewal.AdvanceReady hk ring C e := by
    intro hready
    exact hbar hready.1
  let C1 := step hk ring C e
  have hone1 : OneBarrierAt hk ring C1 b := by
    have hstep := oneBarrier_step hk ring hn2 C b e hndvd hone
    simpa [C1, hnot] using hstep
  have hbar1 : ¬ IsBarrier hk (C1 e) (C1 (ring.rightNeighbor e)) := by
    simpa [C1] using nonbarrier_after_step hk ring C e hbar
  have hnot1 : ¬ CenteredRenewal.AdvanceReady hk ring C1 e := by
    intro hready
    exact hbar1 hready.1
  have hstep := oneBarrier_step hk ring hn2 C1 b e hndvd hone1
  simpa [doubleHit, C1, hnot1] using hstep

/-- Any duplicated word consisting only of ordinary edges keeps the same
physical unique barrier.  Later sweep inductions can therefore discharge each
local nonbarrier premise from one stable witness. -/
theorem runWord_duplicateEdges_parks_unique_barrier {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n) (w : List (Fin n))
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b)
    (hordinary : ∀ e ∈ w, e ≠ b) :
    OneBarrierAt hk ring (runWord hk ring C (duplicateEdges w)) b := by
  induction w generalizing C with
  | nil => simpa using hone
  | cons e w ih =>
      rw [runWord_duplicateEdges_cons]
      apply ih (doubleHit hk ring C e)
      · exact doubleHit_parks_unique_barrier hk ring hn2 C b e hndvd hone
          (hordinary e (by simp))
      · intro f hf
        exact hordinary f (by simp [hf])

/-- A duplicated ordinary word preserves the whole probe vector when every
listed initiator is initially probe-free. -/
theorem runWord_duplicateEdges_preserves_probes_of_clear_initiators
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n) (w : List (Fin n))
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b)
    (hordinary : ∀ e ∈ w, e ≠ b)
    (hclear : ∀ e ∈ w, (C e).probe = false) :
    ∀ i : Fin n,
      (runWord hk ring C (duplicateEdges w) i).probe = (C i).probe := by
  induction w generalizing C with
  | nil => simp
  | cons e w ih =>
      have heOrd : e ≠ b := hordinary e (by simp)
      have hwOrd : ∀ f ∈ w, f ≠ b := by
        intro f hf
        exact hordinary f (by simp [hf])
      have hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
        intro h
        apply heOrd
        exact (hone e).1 ((barrierAt_labelsOf_iff hk ring C e).2 h)
      have heClear : (C e).probe = false := hclear e (by simp)
      have hpair := doubleHit_probes_eq_of_nonbarrier_initiator_clear hk ring
        hn2 C e hbar heClear
      have honeE : OneBarrierAt hk ring (doubleHit hk ring C e) b :=
        doubleHit_parks_unique_barrier hk ring hn2 C b e hndvd hone heOrd
      have hwClear : ∀ f ∈ w, (doubleHit hk ring C e f).probe = false := by
        intro f hf
        rw [hpair f]
        exact hclear f (by simp [hf])
      have hrec := ih (doubleHit hk ring C e) honeE hwOrd hwClear
      intro i
      rw [runWord_duplicateEdges_cons, hrec i, hpair i]

/-- Abstract forward-sweep induction.  Earlier initiators stay out of every
later edge, so their cleared probe bits are framed while the remaining doubled
hits are executed. -/
theorem runWord_duplicateEdges_clears_initiator_probes {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n) (w : List (Fin n))
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b)
    (hordinary : ∀ e ∈ w, e ≠ b)
    (hforward : w.Pairwise
      (fun e f => e ≠ f ∧ e ≠ ring.rightNeighbor f)) :
    let D := runWord hk ring C (duplicateEdges w)
    OneBarrierAt hk ring D b ∧ ∀ e ∈ w, (D e).probe = false := by
  induction w generalizing C with
  | nil => simp [hone]
  | cons e w ih =>
      have heOrd : e ≠ b := hordinary e (by simp)
      have hwOrd : ∀ f ∈ w, f ≠ b := by
        intro f hf
        exact hordinary f (by simp [hf])
      have hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
        intro h
        apply heOrd
        exact (hone e).1 ((barrierAt_labelsOf_iff hk ring C e).2 h)
      have honeE : OneBarrierAt hk ring (doubleHit hk ring C e) b :=
        doubleHit_parks_unique_barrier hk ring hn2 C b e hndvd hone heOrd
      have hhead : ∀ f ∈ w, e ≠ f ∧ e ≠ ring.rightNeighbor f := by
        intro f hf
        exact List.rel_of_pairwise_cons hforward hf
      have htail : w.Pairwise
          (fun x y => x ≠ y ∧ x ≠ ring.rightNeighbor y) :=
        hforward.tail
      have hrec := ih (doubleHit hk ring C e) honeE hwOrd htail
      rw [runWord_duplicateEdges_cons]
      refine ⟨hrec.1, ?_⟩
      intro f hf
      simp only [List.mem_cons] at hf
      rcases hf with hfe | hf
      · subst f
        rw [runWord_duplicateEdges_frame hk ring (doubleHit hk ring C e) w e
          hhead]
        exact doubleHit_probe_clear_of_nonbarrier hk ring hn2 C e hbar
      · exact hrec.2 f hf

/-- Abstract reverse-sweep induction.  An earlier responder is outside every
later edge, so its cleared bullet bit is framed during the remaining word. -/
theorem runWord_duplicateEdges_clears_responder_bullets {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n) (w : List (Fin n))
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b)
    (hordinary : ∀ e ∈ w, e ≠ b)
    (hreverse : w.Pairwise (fun e f =>
      ring.rightNeighbor e ≠ f ∧
        ring.rightNeighbor e ≠ ring.rightNeighbor f)) :
    let D := runWord hk ring C (duplicateEdges w)
    OneBarrierAt hk ring D b ∧
      ∀ e ∈ w, (D (ring.rightNeighbor e)).bullet = false := by
  induction w generalizing C with
  | nil => simp [hone]
  | cons e w ih =>
      have heOrd : e ≠ b := hordinary e (by simp)
      have hwOrd : ∀ f ∈ w, f ≠ b := by
        intro f hf
        exact hordinary f (by simp [hf])
      have hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
        intro h
        apply heOrd
        exact (hone e).1 ((barrierAt_labelsOf_iff hk ring C e).2 h)
      have honeE : OneBarrierAt hk ring (doubleHit hk ring C e) b :=
        doubleHit_parks_unique_barrier hk ring hn2 C b e hndvd hone heOrd
      have hhead : ∀ f ∈ w,
          ring.rightNeighbor e ≠ f ∧
            ring.rightNeighbor e ≠ ring.rightNeighbor f := by
        intro f hf
        exact List.rel_of_pairwise_cons hreverse hf
      have htail : w.Pairwise (fun x y =>
          ring.rightNeighbor x ≠ y ∧
            ring.rightNeighbor x ≠ ring.rightNeighbor y) :=
        hreverse.tail
      have hrec := ih (doubleHit hk ring C e) honeE hwOrd htail
      rw [runWord_duplicateEdges_cons]
      refine ⟨hrec.1, ?_⟩
      intro f hf
      simp only [List.mem_cons] at hf
      rcases hf with hfe | hf
      · subst f
        rw [runWord_duplicateEdges_frame hk ring (doubleHit hk ring C e) w
          (ring.rightNeighbor e) hhead]
        exact doubleHit_responder_bullet_clear_of_nonbarrier hk ring hn2 C e hbar
      · exact hrec.2 f hf

/-- The actual forward doubled cut sweep clears every probe except possibly
the barrier tail, while keeping the barrier parked. -/
theorem forwardSweep_clears_nonTail_probes {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n)
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b) :
    let D := runWord hk ring C (duplicateEdges (cutPathEdges ring b))
    OneBarrierAt hk ring D b ∧
      ∀ i : Fin n, i ≠ b → (D i).probe = false := by
  have hsweep := runWord_duplicateEdges_clears_initiator_probes hk ring hn2
    C b (cutPathEdges ring b) hndvd hone
    (fun e he => mem_cutPathEdges_ne_barrier ring b e he)
    (cutPathEdges_pairwise_forward ring b)
  refine ⟨hsweep.1, ?_⟩
  intro i hi
  exact hsweep.2 i (mem_cutPathEdges_of_ne_barrier ring b i hi)

/-- From any parked one-barrier state, the reverse doubled cut sweep clears
every bullet except possibly the barrier head. -/
theorem reverseSweep_clears_nonHead_bullets {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n)
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b) :
    let path := cutPathEdges ring b
    let D := runWord hk ring C (duplicateEdges path.reverse)
    OneBarrierAt hk ring D b ∧
      ∀ i : Fin n, i ≠ ring.rightNeighbor b → (D i).bullet = false := by
  let path := cutPathEdges ring b
  have hsweep := runWord_duplicateEdges_clears_responder_bullets hk ring hn2
    C b path.reverse hndvd hone
    (by
      intro e he
      exact mem_cutPathEdges_ne_barrier ring b e (by simpa [path] using he))
    (by simpa [path] using cutPathEdges_reverse_pairwise ring b)
  refine ⟨hsweep.1, ?_⟩
  intro i hi
  let e := ring.leftNeighbor i
  have hePath : e ∈ path := by
    exact mem_cutPathEdges_leftNeighbor_of_ne_head ring b i hi
  have heRev : e ∈ path.reverse := by simpa using hePath
  have hclear := hsweep.2 e heRev
  simpa [e, rightNeighbor_leftNeighbor_clean] using hclear

/-- The full parked word establishes exactly the endpoint-sterile invariant
used by the repaired cleanup proof, together with its parked unique barrier. -/
theorem parkedSweepWord_endpointSterile {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n)
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b) :
    let D := runWord hk ring C (parkedSweepWord ring b)
    OneBarrierAt hk ring D b ∧ EndpointSterile ring D b := by
  let path := cutPathEdges ring b
  let F := runWord hk ring C (duplicateEdges path)
  let D := runWord hk ring F (duplicateEdges path.reverse)
  have hfwd : OneBarrierAt hk ring F b ∧
      ∀ i : Fin n, i ≠ b → (F i).probe = false := by
    simpa [F, path] using
      (forwardSweep_clears_nonTail_probes hk ring hn2 C b hndvd hone)
  have hrev : OneBarrierAt hk ring D b ∧
      ∀ i : Fin n, i ≠ ring.rightNeighbor b → (D i).bullet = false := by
    simpa [D, path] using
      (reverseSweep_clears_nonHead_bullets hk ring hn2 F b hndvd hfwd.1)
  have hprobePreserve : ∀ i : Fin n, (D i).probe = (F i).probe := by
    apply runWord_duplicateEdges_preserves_probes_of_clear_initiators hk ring
      hn2 F b path.reverse hndvd hfwd.1
    · intro e he
      exact mem_cutPathEdges_ne_barrier ring b e (by simpa [path] using he)
    · intro e he
      apply hfwd.2 e
      exact mem_cutPathEdges_ne_barrier ring b e (by simpa [path] using he)
  have hresult : OneBarrierAt hk ring D b ∧ EndpointSterile ring D b := by
    refine ⟨hrev.1, ⟨?_, hrev.2⟩⟩
    intro i hi
    rw [hprobePreserve i]
    exact hfwd.2 i hi
  simpa [parkedSweepWord, runWord_append, path, F, D] using hresult

/-- The complete forward/reverse parked word leaves the unique barrier on the
same physical edge. -/
theorem parkedSweepWord_parks_unique_barrier {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n)
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b) :
    OneBarrierAt hk ring (runWord hk ring C (parkedSweepWord ring b)) b := by
  let path := cutPathEdges ring b
  have hordinary : ∀ e ∈ path, e ≠ b := by
    intro e he
    exact mem_cutPathEdges_ne_barrier ring b e he
  have honeForward :
      OneBarrierAt hk ring (runWord hk ring C (duplicateEdges path)) b :=
    runWord_duplicateEdges_parks_unique_barrier hk ring hn2 C b path hndvd
      hone hordinary
  have honeReverse :
      OneBarrierAt hk ring
        (runWord hk ring (runWord hk ring C (duplicateEdges path))
          (duplicateEdges path.reverse)) b := by
    apply runWord_duplicateEdges_parks_unique_barrier hk ring hn2
      (runWord hk ring C (duplicateEdges path)) b path.reverse hndvd
      honeForward
    intro e he
    apply hordinary e
    simpa using he
  simpa [parkedSweepWord, path, runWord_append] using honeReverse

/-- A tail probe is discharged into a leader before either centered phase
branch runs.  In particular, this remains true when the same barrier hit also
advances the barrier. -/
theorem barrier_tail_probe_creates_leader {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (b : Fin n)
    (hbar : IsBarrier hk (C b) (C (ring.rightNeighbor b)))
    (hprobe : (C b).probe = true) :
    ((step hk ring C b) b).leader = true := by
  have htrans : CenteredRenewal.transition hk (C b)
      (C (ring.rightNeighbor b)) =
        CenteredRenewal.barrierStep hk (C b) (C (ring.rightNeighbor b)) :=
    CenteredRenewal.transition_of_barrier hk _ _ hbar
  cases hphase : (C b).phase <;>
    simp [step, PopulationProtocol.step, CenteredRenewal.protocol,
      htrans, CenteredRenewal.barrierStep, hphase, probeHitsBarrier, hprobe]

/-- The phase-zero tail hit cannot advance the centered barrier. -/
theorem barrier_phase_zero_keeps_unique_barrier {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n)
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b)
    (hphase : (C b).phase = false) :
    OneBarrierAt hk ring (step hk ring C b) b := by
  have hnot : ¬ CenteredRenewal.AdvanceReady hk ring C b := by
    intro hready
    exact Bool.noConfusion (hready.2.symm.trans hphase)
  have hstep := oneBarrier_step hk ring hn2 C b b hndvd hone
  simpa [hnot] using hstep

/-- The phase-one tail hit advances unconditionally in the centered protocol,
with the exact new barrier witness and the sanitizer equation above. -/
theorem barrier_phase_one_advances_unique_barrier {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n)
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b)
    (hphase : (C b).phase = true) :
    OneBarrierAt hk ring (step hk ring C b) (ring.rightNeighbor b) := by
  have hbar : IsBarrier hk (C b) (C (ring.rightNeighbor b)) :=
    (barrierAt_labelsOf_iff hk ring C b).mp ((hone b).2 rfl)
  have hready : CenteredRenewal.AdvanceReady hk ring C b := ⟨hbar, hphase⟩
  have hstep := oneBarrier_step hk ring hn2 C b b hndvd hone
  simpa [hready] using hstep

/-- A phase-one barrier hit consumes a unique tail probe, creates exactly one
leader at the old tail, advances the barrier, and leaves the new cut prepared. -/
theorem barrier_phase_one_unique_probe_creates_prepared_leader
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n) (hndvd : ¬ k ∣ n)
    (hone : OneBarrierAt hk ring C b)
    (hphase : (C b).phase = true)
    (hprobe : (C b).probe = true)
    (hprobeUnique : ∀ i : Fin n, i ≠ b → (C i).probe = false)
    (hbulletFrame : ∀ i : Fin n, i ≠ ring.rightNeighbor b →
      (C i).bullet = false)
    (hzero : ∀ i : Fin n, (C i).leader = false) :
    let h := ring.rightNeighbor b
    let D := step hk ring C b
    OneBarrierAt hk ring D h ∧
      (∀ i : Fin n, (D i).bullet = false ∧ (D i).probe = false) ∧
      (D b).leader = true ∧
      (∀ i : Fin n, (D i).leader = true → i = b) := by
  let h := ring.rightNeighbor b
  have hbar : IsBarrier hk (C b) (C h) :=
    (barrierAt_labelsOf_iff hk ring C b).mp ((hone b).2 rfl)
  have htrans : CenteredRenewal.transition hk (C b) (C h) =
      (probeHitsBarrier (C b),
        { C h with
          label := succLabel hk (C b).label
          phase := false
          bullet := false
          probe := false }) := by
    rw [CenteredRenewal.transition_of_barrier hk _ _ hbar]
    exact CenteredRenewal.barrierStep_phase_one hk _ _ hphase
  have hre : h ≠ b := rightNeighbor_ne_self ring hn2 b
  have honeD := barrier_phase_one_advances_unique_barrier hk ring hn2 C b
    hndvd hone hphase
  have hleader := barrier_tail_probe_creates_leader hk ring C b hbar hprobe
  dsimp [h] at htrans hre ⊢
  refine ⟨honeD, ?_, hleader, ?_⟩
  · intro i
    by_cases hib : i = b
    · subst i
      have hb := hbulletFrame b (Ne.symm hre)
      simp [step, PopulationProtocol.step, CenteredRenewal.protocol,
        htrans, probeHitsBarrier, hprobe, hb]
    · by_cases hih : i = ring.rightNeighbor b
      · subst i
        simp [step, PopulationProtocol.step,
          CenteredRenewal.protocol, htrans, hre]
      · have hp := hprobeUnique i hib
        have hb := hbulletFrame i hih
        simp [step, PopulationProtocol.step,
          CenteredRenewal.protocol, hib, hih, hp, hb]
  · intro i hi
    by_cases hib : i = b
    · exact hib
    · by_cases hih : i = ring.rightNeighbor b
      · subst i
        simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
          hre, hzero (ring.rightNeighbor b)] at hi
      · simp [step, PopulationProtocol.step, CenteredRenewal.protocol, hib,
          hih, hzero i] at hi

/-! ## Endpoint discharge and the prepared cut -/

/-- A vertex is free of both mobile control marks.  Labels, phase, and leader
bits are intentionally outside this local preparation predicate. -/
def MarkFree {k : Nat} (q : State k) : Prop :=
  q.bullet = false ∧ q.probe = false

/-- In the cut whose unique physical barrier is `b`, every vertex except the
barrier head is mark-free.  This is the exact postcondition needed before the
leader-guided cleanup circuit starts; it is strictly weaker than `Clean`. -/
def PreparedAt {n k : Nat} (ring : DirectedRing n)
    (C : Fin n → State k) (b : Fin n) : Prop :=
  ∀ i : Fin n, i ≠ ring.rightNeighbor b → MarkFree (C i)

/-- `PreparedAt` is literally the promised statement in the re-cut view:
every non-head cut coordinate is mark-free. -/
theorem PreparedAt.cutView_nonHead {n k : Nat} (ring : DirectedRing n)
    (C : Fin n → State k) (b : Fin n) (hprepared : PreparedAt ring C b) :
    ∀ i : Fin n, i ≠ ⟨0, ring.hn⟩ → MarkFree (cutView ring b C i) := by
  intro i hi
  apply hprepared (cutPos ring b i)
  intro hphysical
  apply hi
  apply cutPos_injective ring b
  simpa using hphysical

/-- For a nontrivial ring the prepared cut's tail is among its protected
non-head vertices. -/
theorem PreparedAt.tail_markFree {n k : Nat} (ring : DirectedRing n)
    (hn2 : 1 < n) (C : Fin n → State k) (b : Fin n)
    (hprepared : PreparedAt ring C b) :
    MarkFree (C b) := by
  apply hprepared b
  exact (rightNeighbor_ne_self ring hn2 b).symm

/-- The endpoint discharge uses no interaction when the parked tail is already
probe-free, and otherwise hits the unique barrier exactly once. -/
def endpointDischargeWord {n k : Nat} (C : Fin n → State k)
    (b : Fin n) : List (Fin n) :=
  if (C b).probe then [b] else []

/-- Exact unique-barrier witness after `endpointDischargeWord`: phase zero
keeps the barrier, while phase one advances it to the old head. -/
def endpointDischargeBarrier {n k : Nat} (ring : DirectedRing n)
    (C : Fin n → State k) (b : Fin n) : Fin n :=
  if (C b).probe then
    if (C b).phase then ring.rightNeighbor b else b
  else
    b

theorem endpointDischargeWord_length_le_one {n k : Nat}
    (C : Fin n → State k) (b : Fin n) :
    (endpointDischargeWord C b).length ≤ 1 := by
  cases hprobe : (C b).probe <;> simp [endpointDischargeWord, hprobe]

/-- Once the exceptional tail probe is absent, endpoint sterility is exactly
enough to prepare the current cut without taking a step. -/
theorem endpointSterile_prepared_of_tail_clear {n k : Nat}
    (ring : DirectedRing n) (C : Fin n → State k) (b : Fin n)
    (hsterile : EndpointSterile ring C b)
    (hprobe : (C b).probe = false) :
    PreparedAt ring C b := by
  intro i hiHead
  refine ⟨hsterile.2 i hiHead, ?_⟩
  by_cases hiTail : i = b
  · simpa [hiTail] using hprobe
  · exact hsterile.1 i hiTail

/-- A phase-zero discharge converts the tail probe to a leader, keeps the
barrier fixed, and may arm only the excluded barrier head. -/
theorem barrier_phase_zero_prepared {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n)
    (hone : OneBarrierAt hk ring C b)
    (hsterile : EndpointSterile ring C b)
    (hprobe : (C b).probe = true)
    (hphase : (C b).phase = false) :
    PreparedAt ring (step hk ring C b) b := by
  have hbar : IsBarrier hk (C b) (C (ring.rightNeighbor b)) :=
    (barrierAt_labelsOf_iff hk ring C b).mp ((hone b).2 rfl)
  have htrans : CenteredRenewal.transition hk (C b)
      (C (ring.rightNeighbor b)) =
        ({ probeHitsBarrier (C b) with phase := true },
          if (C (ring.rightNeighbor b)).leader = false then
            { C (ring.rightNeighbor b) with probe := true }
          else C (ring.rightNeighbor b)) := by
    rw [CenteredRenewal.transition_of_barrier hk _ _ hbar]
    exact CenteredRenewal.barrierStep_phase_zero hk _ _ hphase
  have htailHead : b ≠ ring.rightNeighbor b :=
    (rightNeighbor_ne_self ring hn2 b).symm
  intro i hiHead
  by_cases hiTail : i = b
  · subst i
    have hbullet := hsterile.2 b htailHead
    constructor
    · simpa [MarkFree, step, PopulationProtocol.step,
        CenteredRenewal.protocol, htrans, probeHitsBarrier, hprobe] using
        hbullet
    · simp [step, PopulationProtocol.step,
        CenteredRenewal.protocol, htrans, probeHitsBarrier, hprobe]
  · have hbullet := hsterile.2 i hiHead
    have hprobeI := hsterile.1 i hiTail
    simpa [MarkFree, step, PopulationProtocol.step, CenteredRenewal.protocol,
      htrans, hiTail, hiHead] using And.intro hbullet hprobeI

/-- A phase-one discharge clears both exceptional endpoints: the old tail
probe becomes a leader and the old head, now the new tail, is sanitized.  Thus
the resulting configuration is globally mark-free, a strengthening of the
prepared-cut postcondition. -/
theorem barrier_phase_one_all_markFree {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n)
    (hone : OneBarrierAt hk ring C b)
    (hsterile : EndpointSterile ring C b)
    (hprobe : (C b).probe = true)
    (hphase : (C b).phase = true) :
    ∀ i : Fin n, MarkFree (step hk ring C b i) := by
  have hbar : IsBarrier hk (C b) (C (ring.rightNeighbor b)) :=
    (barrierAt_labelsOf_iff hk ring C b).mp ((hone b).2 rfl)
  have htrans : CenteredRenewal.transition hk (C b)
      (C (ring.rightNeighbor b)) =
        (probeHitsBarrier (C b),
          { C (ring.rightNeighbor b) with
            label := succLabel hk (C b).label
            phase := false
            bullet := false
            probe := false }) := by
    rw [CenteredRenewal.transition_of_barrier hk _ _ hbar]
    exact CenteredRenewal.barrierStep_phase_one hk _ _ hphase
  have htailHead : b ≠ ring.rightNeighbor b :=
    (rightNeighbor_ne_self ring hn2 b).symm
  have hheadTail : ring.rightNeighbor b ≠ b :=
    rightNeighbor_ne_self ring hn2 b
  intro i
  by_cases hiTail : i = b
  · subst i
    have hbullet := hsterile.2 b htailHead
    constructor
    · simpa [MarkFree, step, PopulationProtocol.step,
        CenteredRenewal.protocol, htrans, probeHitsBarrier, hprobe] using
        hbullet
    · simp [step, PopulationProtocol.step,
        CenteredRenewal.protocol, htrans, probeHitsBarrier, hprobe]
  · by_cases hiHead : i = ring.rightNeighbor b
    · subst i
      simp [MarkFree, step, PopulationProtocol.step, CenteredRenewal.protocol,
        htrans, hheadTail]
    · have hbullet := hsterile.2 i hiHead
      have hprobeI := hsterile.1 i hiTail
      simpa [MarkFree, step, PopulationProtocol.step,
        CenteredRenewal.protocol, htrans, hiTail, hiHead] using
        And.intro hbullet hprobeI

theorem barrier_phase_one_prepared {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n)
    (hone : OneBarrierAt hk ring C b)
    (hsterile : EndpointSterile ring C b)
    (hprobe : (C b).probe = true)
    (hphase : (C b).phase = true) :
    PreparedAt ring (step hk ring C b) (ring.rightNeighbor b) := by
  intro i _hiHead
  exact barrier_phase_one_all_markFree hk ring hn2 C b hone hsterile hprobe
    hphase i

/-- The adaptive endpoint discharge is a complete length-at-most-one bridge
from a parked endpoint-sterile state to a prepared cut.  If a tail probe was
present, the selected barrier interaction first converts it into a leader;
the exact phase-zero/phase-one barrier witness is retained. -/
theorem endpointSterile_discharge {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n)
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b)
    (hsterile : EndpointSterile ring C b) :
    let w := endpointDischargeWord C b
    let b' := endpointDischargeBarrier ring C b
    let D := runWord hk ring C w
    w.length ≤ 1 ∧
      OneBarrierAt hk ring D b' ∧
      PreparedAt ring D b' ∧
      ((C b).probe = true → (D b).leader = true) := by
  cases hprobe : (C b).probe with
  | false =>
      simp only [endpointDischargeWord, endpointDischargeBarrier, hprobe,
        Bool.false_eq_true, ↓reduceIte, runWord_nil, List.length_nil,
        Nat.zero_le, true_and]
      exact ⟨hone, endpointSterile_prepared_of_tail_clear ring C b hsterile
        hprobe, nofun⟩
  | true =>
      have hbar : IsBarrier hk (C b) (C (ring.rightNeighbor b)) :=
        (barrierAt_labelsOf_iff hk ring C b).mp ((hone b).2 rfl)
      have hleader := barrier_tail_probe_creates_leader hk ring C b hbar hprobe
      cases hphase : (C b).phase with
      | false =>
          simp only [endpointDischargeWord, endpointDischargeBarrier, hprobe,
            hphase, ↓reduceIte, runWord_cons, runWord_nil, List.length_cons,
            List.length_nil, Nat.reduceAdd]
          exact ⟨by omega,
            barrier_phase_zero_keeps_unique_barrier hk ring hn2 C b hndvd
              hone hphase,
            barrier_phase_zero_prepared hk ring hn2 C b hone hsterile hprobe
              hphase,
            fun _ => hleader⟩
      | true =>
          simp only [endpointDischargeWord, endpointDischargeBarrier, hprobe,
            hphase, ↓reduceIte, runWord_cons, runWord_nil, List.length_cons,
            List.length_nil, Nat.reduceAdd]
          exact ⟨by omega,
            barrier_phase_one_advances_unique_barrier hk ring hn2 C b
              hndvd hone hphase,
            barrier_phase_one_prepared hk ring hn2 C b hone hsterile hprobe
              hphase,
            fun _ => hleader⟩

/-! ## Local equations for the no-leader probe circuit -/

/-- On an ordinary follower edge, one hit transports an initiator probe to
the responder.  A responder bullet does not interfere because the literal
ordinary branch moves the bullet before it moves the probe. -/
theorem nonbarrier_follower_probe_progress {k : Nat} (u v : State k)
    (hfollower : v.leader = false) (hprobe : u.probe = true) :
    let z := nonBarrierStep u v
    z.1.probe = false ∧ z.2.probe = true := by
  cases hbullet : v.bullet <;>
    simp [nonBarrierStep, hfollower, hbullet, hprobe]

/-- Packaged configuration form of one-step follower probe transport. -/
theorem step_follower_probe_progress_of_nonbarrier {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)))
    (hfollower : (C (ring.rightNeighbor e)).leader = false)
    (hprobe : (C e).probe = true) :
    (step hk ring C e e).probe = false ∧
      (step hk ring C e (ring.rightNeighbor e)).probe = true := by
  have hlocal := nonbarrier_follower_probe_progress
    (C e) (C (ring.rightNeighbor e)) hfollower hprobe
  have htrans : CenteredRenewal.transition hk (C e)
      (C (ring.rightNeighbor e)) =
        nonBarrierStep (C e) (C (ring.rightNeighbor e)) :=
    CenteredRenewal.transition_of_nonbarrier hk _ _ hbar
  have hre : ring.rightNeighbor e ≠ e := rightNeighbor_ne_self ring hn2 e
  constructor
  · simpa [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
      hre.symm] using hlocal.1
  · simpa [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
      hre] using hlocal.2

/-- The same follower transport also records the bullet frame needed by the
zero-leader circuit: a bullet-free responder stays bullet-free, the
initiator's bullet is unchanged, and all other sites are literally framed. -/
theorem step_follower_probe_mark_progress_of_nonbarrier {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)))
    (hfollower : (C (ring.rightNeighbor e)).leader = false)
    (hprobe : (C e).probe = true)
    (hrespBullet : (C (ring.rightNeighbor e)).bullet = false) :
    (step hk ring C e e).probe = false ∧
      (step hk ring C e (ring.rightNeighbor e)).probe = true ∧
      (step hk ring C e e).bullet = (C e).bullet ∧
      (step hk ring C e (ring.rightNeighbor e)).bullet = false ∧
      (∀ i : Fin n, i ≠ e → i ≠ ring.rightNeighbor e →
        step hk ring C e i = C i) := by
  have htrans : CenteredRenewal.transition hk (C e)
      (C (ring.rightNeighbor e)) =
        nonBarrierStep (C e) (C (ring.rightNeighbor e)) :=
    CenteredRenewal.transition_of_nonbarrier hk _ _ hbar
  have hre : ring.rightNeighbor e ≠ e := rightNeighbor_ne_self ring hn2 e
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
      nonBarrierStep, hfollower, hrespBullet, hprobe]
  · simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
      nonBarrierStep, hfollower, hrespBullet, hprobe, hre]
  · simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
      nonBarrierStep, hfollower, hrespBullet, hprobe]
  · simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
      nonBarrierStep, hfollower, hrespBullet, hprobe, hre]
  · intro i hie hir
    simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
      nonBarrierStep, hfollower, hrespBullet, hprobe, hie, hir]

theorem step_phases_eq_of_nonbarrier {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (e : Fin n)
    (hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e))) :
    ∀ i : Fin n, (step hk ring C e i).phase = (C i).phase := by
  have htrans : CenteredRenewal.transition hk (C e)
      (C (ring.rightNeighbor e)) =
        nonBarrierStep (C e) (C (ring.rightNeighbor e)) :=
    CenteredRenewal.transition_of_nonbarrier hk _ _ hbar
  cases hleader : (C (ring.rightNeighbor e)).leader <;>
    cases hbullet : (C (ring.rightNeighbor e)).bullet <;>
    cases hprobe : (C e).probe
  all_goals
    intro i
    by_cases hie : i = e
    · subst i
      simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
        nonBarrierStep, hleader, hbullet, hprobe]
    · by_cases hir : i = ring.rightNeighbor e
      · subst i
        simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
          nonBarrierStep, hleader, hbullet, hprobe, hie]
      · simp [step, PopulationProtocol.step, CenteredRenewal.protocol, hie, hir]

/-- A phase-zero barrier hit against a follower arms the tail, leaves its
probe clear after the source-order `probeHitsBarrier` prelude, and installs a
probe on the head. -/
theorem barrier_phase_zero_arms_follower_head {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n)
    (hbar : IsBarrier hk (C b) (C (ring.rightNeighbor b)))
    (hphase : (C b).phase = false)
    (hfollower : (C (ring.rightNeighbor b)).leader = false) :
    ((step hk ring C b) b).phase = true ∧
      ((step hk ring C b) b).probe = false ∧
      ((step hk ring C b) (ring.rightNeighbor b)).probe = true := by
  have htrans : CenteredRenewal.transition hk (C b)
      (C (ring.rightNeighbor b)) =
        ({ probeHitsBarrier (C b) with phase := true },
          { C (ring.rightNeighbor b) with probe := true }) := by
    rw [CenteredRenewal.transition_of_barrier hk _ _ hbar]
    rw [CenteredRenewal.barrierStep_phase_zero hk _ _ hphase]
    simp [hfollower]
  have hre : ring.rightNeighbor b ≠ b := rightNeighbor_ne_self ring hn2 b
  cases hprobe : (C b).probe <;>
    simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
      hre, probeHitsBarrier, hprobe]

/-- Starting from an endpoint-sterile, leader-free cut with a clear tail,
the phase-zero barrier hit creates the unique probe at the head and preserves
the single possible bullet anchor there. -/
theorem barrier_phase_zero_starts_probe_circuit {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n) (hndvd : ¬ k ∣ n)
    (hone : OneBarrierAt hk ring C b)
    (hsterile : EndpointSterile ring C b)
    (hphase : (C b).phase = false)
    (htailProbe : (C b).probe = false)
    (hzero : ∀ i : Fin n, (C i).leader = false) :
    let h := ring.rightNeighbor b
    let D := step hk ring C b
    OneBarrierAt hk ring D b ∧
      (D b).phase = true ∧
      (D h).probe = true ∧
      (∀ i : Fin n, i ≠ h → (D i).probe = false) ∧
      (∀ i : Fin n, i ≠ h → (D i).bullet = false) ∧
      (∀ i : Fin n, (D i).leader = false) := by
  let h := ring.rightNeighbor b
  have hbar : IsBarrier hk (C b) (C h) := by
    exact (barrierAt_labelsOf_iff hk ring C b).mp ((hone b).2 rfl)
  have htrans : CenteredRenewal.transition hk (C b) (C h) =
      ({ probeHitsBarrier (C b) with phase := true },
        { C h with probe := true }) := by
    rw [CenteredRenewal.transition_of_barrier hk _ _ hbar]
    rw [CenteredRenewal.barrierStep_phase_zero hk _ _ hphase]
    simp [hzero h]
  have hre : h ≠ b := rightNeighbor_ne_self ring hn2 b
  have honeD := barrier_phase_zero_keeps_unique_barrier hk ring hn2 C b hndvd
    hone hphase
  have harm := barrier_phase_zero_arms_follower_head hk ring hn2 C b hbar
    hphase (hzero h)
  dsimp [h] at htrans hre ⊢
  refine ⟨honeD, harm.1, harm.2.2, ?_, ?_, ?_⟩
  · intro i hih
    by_cases hib : i = b
    · subst i
      simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
        probeHitsBarrier, htailProbe]
    · have hip := hsterile.1 i hib
      simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
        hib, hih, hip]
  · intro i hih
    by_cases hib : i = b
    · subst i
      have hb := hsterile.2 b (Ne.symm hre)
      simpa [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
        probeHitsBarrier, htailProbe] using hb
    · have hibullet := hsterile.2 i hih
      simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
        hib, hih, hibullet]
  · intro i
    by_cases hib : i = b
    · subst i
      simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
        probeHitsBarrier, htailProbe, hzero b]
    · by_cases hih : i = h
      · subst i
        simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
          h, hre, hzero (ring.rightNeighbor b)]
      · have hih' : i ≠ ring.rightNeighbor b := by simpa [h] using hih
        simp [step, PopulationProtocol.step, CenteredRenewal.protocol, hib,
          hih', hzero i]

/-! ## Advancing across a leader at the barrier head -/

/-- When the parked tail is probe-free, a phase-one barrier advance preserves
the complete leader vector.  The responder sanitizer changes only its label,
phase, bullet, and probe fields. -/
theorem barrier_phase_one_leaders_eq {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n)
    (hone : OneBarrierAt hk ring C b)
    (hphase : (C b).phase = true)
    (htailProbe : (C b).probe = false) :
    ∀ i : Fin n, ((step hk ring C b) i).leader = (C i).leader := by
  have hbar : IsBarrier hk (C b) (C (ring.rightNeighbor b)) :=
    (barrierAt_labelsOf_iff hk ring C b).mp ((hone b).2 rfl)
  have htrans : CenteredRenewal.transition hk (C b)
      (C (ring.rightNeighbor b)) =
        (probeHitsBarrier (C b),
          { C (ring.rightNeighbor b) with
            label := succLabel hk (C b).label
            phase := false
            bullet := false
            probe := false }) := by
    rw [CenteredRenewal.transition_of_barrier hk _ _ hbar]
    exact CenteredRenewal.barrierStep_phase_one hk _ _ hphase
  have hre : ring.rightNeighbor b ≠ b := rightNeighbor_ne_self ring hn2 b
  intro i
  by_cases hib : i = b
  · subst i
    simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
      probeHitsBarrier, htailProbe]
  · by_cases hih : i = ring.rightNeighbor b
    · subst i
      simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
        hre]
    · simp [step, PopulationProtocol.step, CenteredRenewal.protocol,
        hib, hih]

/-- The phase-zero arm hit is harmless when its tail is probe-free and its
head is already a leader: it only flips the tail phase.  In particular it
keeps the tail probe clear and preserves every leader bit. -/
theorem barrier_phase_zero_over_head_leader {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n)
    (hone : OneBarrierAt hk ring C b)
    (hphase : (C b).phase = false)
    (htailProbe : (C b).probe = false)
    (hhead : (C (ring.rightNeighbor b)).leader = true) :
    ((step hk ring C b) b).phase = true ∧
      ((step hk ring C b) b).probe = false ∧
      (∀ i : Fin n, ((step hk ring C b) i).leader = (C i).leader) := by
  have hbar : IsBarrier hk (C b) (C (ring.rightNeighbor b)) :=
    (barrierAt_labelsOf_iff hk ring C b).mp ((hone b).2 rfl)
  have htrans : CenteredRenewal.transition hk (C b)
      (C (ring.rightNeighbor b)) =
        ({ C b with phase := true }, C (ring.rightNeighbor b)) := by
    rw [CenteredRenewal.transition_of_barrier hk _ _ hbar]
    rw [CenteredRenewal.barrierStep_phase_zero hk _ _ hphase]
    simp [probeHitsBarrier, htailProbe, hhead]
  have hre : ring.rightNeighbor b ≠ b := rightNeighbor_ne_self ring hn2 b
  refine ⟨?_, ?_, ?_⟩
  · simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans]
  · simpa [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans]
      using htailProbe
  · intro i
    by_cases hib : i = b
    · subst i
      simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans]
    · by_cases hih : i = ring.rightNeighbor b
      · subst i
        simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
          hre]
      · simp [step, PopulationProtocol.step, CenteredRenewal.protocol,
          hib, hih]

/-- One hit suffices when the tail is armed; otherwise the first hit arms it
and the second advances. -/
def advanceOverHeadLeaderWord {n k : Nat} (C : Fin n → State k)
    (b : Fin n) : List (Fin n) :=
  if (C b).phase then [b] else [b, b]

theorem advanceOverHeadLeaderWord_length_le_two {n k : Nat}
    (C : Fin n → State k) (b : Fin n) :
    (advanceOverHeadLeaderWord C b).length ≤ 2 := by
  cases hphase : (C b).phase <;>
    simp [advanceOverHeadLeaderWord, hphase]

/-- A probe-free parked tail advances across a leader head in at most two
barrier hits.  The old head is the new unique-barrier tail, is mark-free after
the centered sanitizer, and the full leader vector is framed. -/
theorem advance_over_head_leader {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n)
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b)
    (htailProbe : (C b).probe = false)
    (hhead : (C (ring.rightNeighbor b)).leader = true) :
    let w := advanceOverHeadLeaderWord C b
    let h := ring.rightNeighbor b
    let D := runWord hk ring C w
    w.length ≤ 2 ∧
      OneBarrierAt hk ring D h ∧
      (D h).leader = true ∧
      MarkFree (D h) ∧
      (∀ i : Fin n, (D i).leader = (C i).leader) := by
  cases hphase : (C b).phase with
  | true =>
      have honeD := barrier_phase_one_advances_unique_barrier hk ring hn2 C b
        hndvd hone hphase
      have hfresh := advance_sanitizes_new_tail hk ring hn2 C b hone hphase
      have hleaders := barrier_phase_one_leaders_eq hk ring hn2 C b hone
        hphase htailProbe
      simp only [advanceOverHeadLeaderWord, hphase, ↓reduceIte, runWord_cons,
        runWord_nil, List.length_cons, List.length_nil, Nat.reduceAdd]
      refine ⟨by omega, honeD, ?_, ⟨hfresh.2.1, hfresh.2.2⟩, hleaders⟩
      rw [hleaders]
      exact hhead
  | false =>
      let C₁ := step hk ring C b
      have harm := barrier_phase_zero_over_head_leader hk ring hn2 C b hone
        hphase htailProbe hhead
      have hone₁ : OneBarrierAt hk ring C₁ b := by
        exact barrier_phase_zero_keeps_unique_barrier hk ring hn2 C b hndvd
          hone hphase
      have honeD := barrier_phase_one_advances_unique_barrier hk ring hn2 C₁ b
        hndvd hone₁ harm.1
      have hfresh := advance_sanitizes_new_tail hk ring hn2 C₁ b hone₁
        harm.1
      have hleaders₁ := harm.2.2
      have hleadersD := barrier_phase_one_leaders_eq hk ring hn2 C₁ b hone₁
        harm.1 harm.2.1
      simp only [advanceOverHeadLeaderWord, hphase, Bool.false_eq_true,
        ↓reduceIte, runWord_cons, runWord_nil, List.length_cons,
        List.length_nil, Nat.reduceAdd]
      refine ⟨by omega, honeD, ?_, ⟨hfresh.2.1, hfresh.2.2⟩, ?_⟩
      · rw [hleadersD, hleaders₁]
        exact hhead
      · intro i
        rw [hleadersD i, hleaders₁ i]

/-! ## The final tracked-bullet corridor -/

/-- The minimal state needed to start the terminal corridor.  Interior marks
and leaders are deliberately unrestricted: the tracked bullet removes every
leader it meets, while exact `Clean` only protects the surviving tail. -/
structure FinalCorridorReady {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (b : Fin n) : Prop where
  barrier : OneBarrierAt hk ring C b
  tailLeader : (C b).leader = true
  tailFresh : MarkFree (C b)
  headFollower : (C (ring.rightNeighbor b)).leader = false

/-- Consecutive edges in a backward corridor meet head-to-tail: the initiator
of the preceding doubled hit is the responder of the next one. -/
def BackwardBulletChain {n : Nat} (ring : DirectedRing n) :
    List (Fin n) → Prop
  | [] => True
  | [_] => True
  | e :: f :: w => ring.rightNeighbor f = e ∧ BackwardBulletChain ring (f :: w)

/-- Local induction for the final corridor.  A tracked responder bullet moves
backward through a nonempty chain of doubled ordinary edges.  At the end it is
on the last initiator, and every responder visited by the chain is a follower.
The reverse-pairwise premise is exactly the frame condition that prevents a
later doubled hit from revisiting an already cleared responder. -/
theorem runWord_duplicateEdges_tracks_bullet {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b e : Fin n) (w : List (Fin n))
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b)
    (hordinary : ∀ f ∈ e :: w, f ≠ b)
    (hreverse : (e :: w).Pairwise (fun x y =>
      ring.rightNeighbor x ≠ y ∧
        ring.rightNeighbor x ≠ ring.rightNeighbor y))
    (hchain : BackwardBulletChain ring (e :: w))
    (hbullet : (C (ring.rightNeighbor e)).bullet = true) :
    let D := runWord hk ring C (duplicateEdges (e :: w))
    OneBarrierAt hk ring D b ∧
      (D ((e :: w).getLast (by simp))).bullet = true ∧
      (∀ f ∈ e :: w, (D (ring.rightNeighbor f)).leader = false) := by
  induction w generalizing C e with
  | nil =>
      have heOrd : e ≠ b := hordinary e (by simp)
      have hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
        intro h
        apply heOrd
        exact (hone e).1 ((barrierAt_labelsOf_iff hk ring C e).2 h)
      have honeD := doubleHit_parks_unique_barrier hk ring hn2 C b e hndvd
        hone heOrd
      have hprogress := doubleHit_bullet_progress_of_nonbarrier hk ring hn2
        C e hbar hbullet
      simp only [duplicateEdges_cons, duplicateEdges_nil, runWord_cons,
        runWord_nil]
      refine ⟨honeD, ?_, ?_⟩
      · simpa using hprogress.1
      · intro f hf
        simp only [List.mem_singleton] at hf
        subst f
        exact hprogress.2.2.2
  | cons f w ih =>
      have heOrd : e ≠ b := hordinary e (by simp)
      have hfwOrd : ∀ g ∈ f :: w, g ≠ b := by
        intro g hg
        exact hordinary g (by simp [hg])
      have hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
        intro h
        apply heOrd
        exact (hone e).1 ((barrierAt_labelsOf_iff hk ring C e).2 h)
      have honeE := doubleHit_parks_unique_barrier hk ring hn2 C b e hndvd
        hone heOrd
      have hprogress := doubleHit_bullet_progress_of_nonbarrier hk ring hn2
        C e hbar hbullet
      have hmeet : ring.rightNeighbor f = e := hchain.1
      have hchainTail : BackwardBulletChain ring (f :: w) := hchain.2
      have hreverseTail : (f :: w).Pairwise (fun x y =>
          ring.rightNeighbor x ≠ y ∧
            ring.rightNeighbor x ≠ ring.rightNeighbor y) :=
        hreverse.tail
      have hbulletTail :
          (doubleHit hk ring C e (ring.rightNeighbor f)).bullet = true := by
        rw [hmeet]
        exact hprogress.1
      have hrec := ih (doubleHit hk ring C e) f honeE hfwOrd hreverseTail
        hchainTail hbulletTail
      rw [runWord_duplicateEdges_cons]
      refine ⟨hrec.1, ?_, ?_⟩
      · simpa only [List.getLast_cons_cons] using hrec.2.1
      · intro g hg
        simp only [List.mem_cons] at hg
        rcases hg with hge | hg
        · subst g
          have hframe : ∀ q ∈ f :: w,
              ring.rightNeighbor e ≠ q ∧
                ring.rightNeighbor e ≠ ring.rightNeighbor q := by
            intro q hq
            exact List.rel_of_pairwise_cons hreverse hq
          rw [runWord_duplicateEdges_frame hk ring (doubleHit hk ring C e)
            (f :: w) (ring.rightNeighbor e) hframe]
          exact hprogress.2.2.2
        · exact hrec.2.2 g (by simp [hg])

/-! ## The no-leader probe corridor -/

/-- Consecutive edges in a forward probe corridor share the transported
vertex: the responder of one hit is the initiator of the next. -/
def ForwardProbeChain {n : Nat} (ring : DirectedRing n) :
    List (Fin n) → Prop
  | [] => True
  | [_] => True
  | e :: f :: w => ring.rightNeighbor e = f ∧ ForwardProbeChain ring (f :: w)

/-- Physical forward edge walk, used to instantiate the probe-chain induction
without any auxiliary rank API. -/
def forwardEdgeWalk {n : Nat} (ring : DirectedRing n) (e : Fin n) :
    Nat → List (Fin n)
  | 0 => []
  | m + 1 => e :: forwardEdgeWalk ring (ring.rightNeighbor e) m

@[simp] theorem forwardEdgeWalk_length {n : Nat} (ring : DirectedRing n)
    (e : Fin n) (m : Nat) : (forwardEdgeWalk ring e m).length = m := by
  induction m generalizing e with
  | zero => rfl
  | succ m ih => simp [forwardEdgeWalk, ih]

theorem forwardEdgeWalk_chain {n : Nat} (ring : DirectedRing n)
    (e : Fin n) (m : Nat) : ForwardProbeChain ring (forwardEdgeWalk ring e m) := by
  cases m with
  | zero => trivial
  | succ m =>
      induction m generalizing e with
      | zero => trivial
      | succ m ih => exact ⟨rfl, ih (ring.rightNeighbor e)⟩

/-- Physical backward edge walk, used by both Corridor A and the final
tail-survivor corridor. -/
def backwardEdgeWalk {n : Nat} (ring : DirectedRing n) (e : Fin n) :
    Nat → List (Fin n)
  | 0 => []
  | m + 1 => e :: backwardEdgeWalk ring (ring.leftNeighbor e) m

@[simp] theorem backwardEdgeWalk_length {n : Nat} (ring : DirectedRing n)
    (e : Fin n) (m : Nat) : (backwardEdgeWalk ring e m).length = m := by
  induction m generalizing e with
  | zero => rfl
  | succ m ih => simp [backwardEdgeWalk, ih]

theorem backwardEdgeWalk_chain {n : Nat} (ring : DirectedRing n)
    (e : Fin n) (m : Nat) :
    BackwardBulletChain ring (backwardEdgeWalk ring e m) := by
  cases m with
  | zero => trivial
  | succ m =>
      induction m generalizing e with
      | zero => trivial
      | succ m ih =>
          exact ⟨rightNeighbor_leftNeighbor_clean ring e,
            ih (ring.leftNeighbor e)⟩

/-- A finite forward chain of ordinary single hits transports a probe to the
last responder.  Starting from a leader-free configuration, every intermediate
configuration remains leader-free and the unique barrier stays parked.  This
is the deterministic local induction needed by the no-leader terminal arm. -/
theorem runWord_tracks_probe_no_leaders {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b e : Fin n) (w : List (Fin n))
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b)
    (hordinary : ∀ f ∈ e :: w, f ≠ b)
    (hchain : ForwardProbeChain ring (e :: w))
    (hprobe : (C e).probe = true)
    (hzero : ∀ i : Fin n, (C i).leader = false) :
    let D := runWord hk ring C (e :: w)
    OneBarrierAt hk ring D b ∧
      (D (ring.rightNeighbor ((e :: w).getLast (by simp)))).probe = true ∧
      (∀ i : Fin n, (D i).leader = false) := by
  induction w generalizing C e with
  | nil =>
      have heOrd : e ≠ b := hordinary e (by simp)
      have hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
        intro h
        apply heOrd
        exact (hone e).1 ((barrierAt_labelsOf_iff hk ring C e).2 h)
      have hnot : ¬ CenteredRenewal.AdvanceReady hk ring C e := by
        intro hready
        exact hbar hready.1
      have honeD := oneBarrier_step hk ring hn2 C b e hndvd hone
      have hmove := step_follower_probe_progress_of_nonbarrier hk ring hn2
        C e hbar (hzero _) hprobe
      have hzeroD : ∀ i : Fin n, ((step hk ring C e) i).leader = false := by
        intro i
        cases hi : ((step hk ring C e) i).leader with
        | false => rfl
        | true =>
            have hold := step_no_leader_birth_of_nonbarrier hk ring hn2 C e
              hbar i hi
            exact False.elim (Bool.noConfusion ((hzero i).symm.trans hold))
      simp only [runWord_cons, runWord_nil]
      refine ⟨?_, ?_, hzeroD⟩
      · simpa [hnot] using honeD
      · simpa using hmove.2
  | cons f w ih =>
      have heOrd : e ≠ b := hordinary e (by simp)
      have hfwOrd : ∀ g ∈ f :: w, g ≠ b := by
        intro g hg
        exact hordinary g (by simp [hg])
      have hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
        intro h
        apply heOrd
        exact (hone e).1 ((barrierAt_labelsOf_iff hk ring C e).2 h)
      have hnot : ¬ CenteredRenewal.AdvanceReady hk ring C e := by
        intro hready
        exact hbar hready.1
      have honeE0 := oneBarrier_step hk ring hn2 C b e hndvd hone
      have honeE : OneBarrierAt hk ring (step hk ring C e) b := by
        simpa [hnot] using honeE0
      have hmove := step_follower_probe_progress_of_nonbarrier hk ring hn2
        C e hbar (hzero _) hprobe
      have hzeroE : ∀ i : Fin n, ((step hk ring C e) i).leader = false := by
        intro i
        cases hi : ((step hk ring C e) i).leader with
        | false => rfl
        | true =>
            have hold := step_no_leader_birth_of_nonbarrier hk ring hn2 C e
              hbar i hi
            exact False.elim (Bool.noConfusion ((hzero i).symm.trans hold))
      have hmeet : ring.rightNeighbor e = f := hchain.1
      have hprobeF : ((step hk ring C e) f).probe = true := by
        rw [← hmeet]
        exact hmove.2
      have hrec := ih (step hk ring C e) f honeE hfwOrd hchain.2 hprobeF
        hzeroE
      simpa only [runWord_cons, List.getLast_cons_cons] using hrec

/-- Strengthened probe-chain induction used only by the zero-leader arm.
Besides transporting the unique probe, it preserves the invariant that every
bullet outside one fixed anchor is absent. -/
theorem runWord_tracks_unique_probe_mark_frame {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b a e : Fin n) (w : List (Fin n))
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b)
    (hordinary : ∀ f ∈ e :: w, f ≠ b)
    (hchain : ForwardProbeChain ring (e :: w))
    (hprobe : (C e).probe = true)
    (hprobeUnique : ∀ i : Fin n, i ≠ e → (C i).probe = false)
    (hbulletFrame : ∀ i : Fin n, i ≠ a → (C i).bullet = false)
    (hanchorAvoid : ∀ f ∈ e :: w, ring.rightNeighbor f ≠ a)
    (hzero : ∀ i : Fin n, (C i).leader = false) :
    let t := ring.rightNeighbor ((e :: w).getLast (by simp))
    let D := runWord hk ring C (e :: w)
    OneBarrierAt hk ring D b ∧
      (D t).probe = true ∧
      (∀ i : Fin n, i ≠ t → (D i).probe = false) ∧
      (∀ i : Fin n, i ≠ a → (D i).bullet = false) ∧
      (∀ i : Fin n, (D i).leader = false) ∧
      (∀ i : Fin n, (D i).phase = (C i).phase) := by
  induction w generalizing C e with
  | nil =>
      have heOrd : e ≠ b := hordinary e (by simp)
      have hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
        intro h
        apply heOrd
        exact (hone e).1 ((barrierAt_labelsOf_iff hk ring C e).2 h)
      have hnot : ¬ CenteredRenewal.AdvanceReady hk ring C e := by
        intro hready
        exact hbar hready.1
      have honeD0 := oneBarrier_step hk ring hn2 C b e hndvd hone
      have honeD : OneBarrierAt hk ring (step hk ring C e) b := by
        simpa [hnot] using honeD0
      have hrespBullet : (C (ring.rightNeighbor e)).bullet = false :=
        hbulletFrame _ (hanchorAvoid e (by simp))
      have hmove := step_follower_probe_mark_progress_of_nonbarrier hk ring
        hn2 C e hbar (hzero _) hprobe hrespBullet
      have hzeroD : ∀ i : Fin n, ((step hk ring C e) i).leader = false := by
        intro i
        cases hi : ((step hk ring C e) i).leader with
        | false => rfl
        | true =>
            have hold := step_no_leader_birth_of_nonbarrier hk ring hn2 C e
              hbar i hi
            exact False.elim (Bool.noConfusion ((hzero i).symm.trans hold))
      have hphaseD := step_phases_eq_of_nonbarrier hk ring C e hbar
      simp only [runWord_cons, runWord_nil, List.getLast_singleton]
      refine ⟨honeD, hmove.2.1, ?_, ?_, hzeroD, hphaseD⟩
      · intro i hit
        by_cases hie : i = e
        · subst i
          exact hmove.1
        · exact (congrArg State.probe (hmove.2.2.2.2 i hie hit)).trans
            (hprobeUnique i hie)
      · intro i hia
        by_cases hie : i = e
        · subst i
          rw [hmove.2.2.1]
          exact hbulletFrame e hia
        · by_cases hir : i = ring.rightNeighbor e
          · subst i
            exact hmove.2.2.2.1
          · exact (congrArg State.bullet (hmove.2.2.2.2 i hie hir)).trans
              (hbulletFrame i hia)
  | cons f w ih =>
      have heOrd : e ≠ b := hordinary e (by simp)
      have hfwOrd : ∀ g ∈ f :: w, g ≠ b := by
        intro g hg
        exact hordinary g (by simp [hg])
      have hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
        intro h
        apply heOrd
        exact (hone e).1 ((barrierAt_labelsOf_iff hk ring C e).2 h)
      have hnot : ¬ CenteredRenewal.AdvanceReady hk ring C e := by
        intro hready
        exact hbar hready.1
      have honeE0 := oneBarrier_step hk ring hn2 C b e hndvd hone
      have honeE : OneBarrierAt hk ring (step hk ring C e) b := by
        simpa [hnot] using honeE0
      have hmeet : ring.rightNeighbor e = f := hchain.1
      have hrespBullet : (C (ring.rightNeighbor e)).bullet = false :=
        hbulletFrame _ (hanchorAvoid e (by simp))
      have hmove := step_follower_probe_mark_progress_of_nonbarrier hk ring
        hn2 C e hbar (hzero _) hprobe hrespBullet
      have hprobeF : ((step hk ring C e) f).probe = true := by
        rw [← hmeet]
        exact hmove.2.1
      have hprobeUniqueE : ∀ i : Fin n, i ≠ f →
          ((step hk ring C e) i).probe = false := by
        intro i hif
        by_cases hie : i = e
        · subst i
          exact hmove.1
        · exact (congrArg State.probe (hmove.2.2.2.2 i hie (by
            simpa [hmeet] using hif))).trans (hprobeUnique i hie)
      have hbulletFrameE : ∀ i : Fin n, i ≠ a →
          ((step hk ring C e) i).bullet = false := by
        intro i hia
        by_cases hie : i = e
        · subst i
          rw [hmove.2.2.1]
          exact hbulletFrame e hia
        · by_cases hir : i = ring.rightNeighbor e
          · subst i
            exact hmove.2.2.2.1
          · exact (congrArg State.bullet (hmove.2.2.2.2 i hie hir)).trans
              (hbulletFrame i hia)
      have hanchorTail : ∀ g ∈ f :: w, ring.rightNeighbor g ≠ a := by
        intro g hg
        exact hanchorAvoid g (by simp [hg])
      have hzeroE : ∀ i : Fin n, ((step hk ring C e) i).leader = false := by
        intro i
        cases hi : ((step hk ring C e) i).leader with
        | false => rfl
        | true =>
            have hold := step_no_leader_birth_of_nonbarrier hk ring hn2 C e
              hbar i hi
            exact False.elim (Bool.noConfusion ((hzero i).symm.trans hold))
      have hrec := ih (step hk ring C e) f honeE hfwOrd hchain.2 hprobeF
        hprobeUniqueE hbulletFrameE hanchorTail hzeroE
      have hphaseE := step_phases_eq_of_nonbarrier hk ring C e hbar
      refine ⟨hrec.1, hrec.2.1, hrec.2.2.1, hrec.2.2.2.1,
        hrec.2.2.2.2.1, ?_⟩
      intro i
      change (runWord hk ring (step hk ring C e) (f :: w) i).phase =
        (C i).phase
      rw [hrec.2.2.2.2.2 i, hphaseE i]

/-! ## Constructive rightmost-leader selection -/

/-- Leader coordinates in the current barrier cut, in increasing cut order. -/
def leaderCutCoords {n k : Nat} (ring : DirectedRing n)
    (C : Fin n → State k) (b : Fin n) : List (Fin n) :=
  (List.finRange n).filter
    (fun i => (C (cutPos ring b i)).leader)

/-- A physical leader of maximum cut coordinate. -/
def RightmostLeader {n k : Nat} (ring : DirectedRing n)
    (C : Fin n → State k) (b R : Fin n) : Prop :=
  (C R).leader = true ∧
    ∀ x : Fin n, (C x).leader = true →
      (cutCoord ring b x).val ≤ (cutCoord ring b R).val

theorem mem_leaderCutCoords_iff {n k : Nat} (ring : DirectedRing n)
    (C : Fin n → State k) (b i : Fin n) :
    i ∈ leaderCutCoords ring C b ↔
      (C (cutPos ring b i)).leader = true := by
  simp [leaderCutCoords]

/-- The finite cut scan supplies a concrete maximum-rank leader whenever the
configuration contains a leader. -/
theorem exists_rightmostLeader {n k : Nat} (ring : DirectedRing n)
    (C : Fin n → State k) (b : Fin n)
    (hHas : ∃ x : Fin n, (C x).leader = true) :
    ∃ R : Fin n, RightmostLeader ring C b R := by
  classical
  have hcoords : leaderCutCoords ring C b ≠ [] := by
    obtain ⟨x, hx⟩ := hHas
    intro hempty
    have hm : cutCoord ring b x ∈ leaderCutCoords ring C b :=
      (mem_leaderCutCoords_iff ring C b (cutCoord ring b x)).2 (by
        simpa using hx)
    rw [hempty] at hm
    simp at hm
  let r : Fin n := List.maxOn Fin.val (leaderCutCoords ring C b) hcoords
  refine ⟨cutPos ring b r, ?_, ?_⟩
  · exact (mem_leaderCutCoords_iff ring C b r).1
      (List.maxOn_mem (f := Fin.val) (xs := leaderCutCoords ring C b))
  · intro x hx
    have hm : cutCoord ring b x ∈ leaderCutCoords ring C b :=
      (mem_leaderCutCoords_iff ring C b (cutCoord ring b x)).2 (by
        simpa using hx)
    have hmax := List.le_apply_maxOn_of_mem (f := Fin.val) hm
    simpa [r] using hmax

/-! ## Cut-prefix words consumed by the two leader corridors -/

/-- Ordinary cut edges strictly before physical site `R`. -/
def cutPrefixEdges {n : Nat} (ring : DirectedRing n) (b R : Fin n) :
    List (Fin n) :=
  (cutPathEdges ring b).take (cutCoord ring b R).val

theorem cutPrefixEdges_length {n : Nat} (ring : DirectedRing n)
    (b R : Fin n) :
    (cutPrefixEdges ring b R).length = (cutCoord ring b R).val := by
  rw [cutPrefixEdges, List.length_take, cutPathEdges_length]
  have hr := (cutCoord ring b R).isLt
  omega

theorem mem_cutPrefixEdges_ne_barrier {n : Nat} (ring : DirectedRing n)
    (b R e : Fin n) (he : e ∈ cutPrefixEdges ring b R) : e ≠ b := by
  apply mem_cutPathEdges_ne_barrier ring b e
  exact List.mem_of_mem_take he

/-- Reversing a cut prefix inherits the endpoint-disjoint frame relation from
the complete reverse cut path. -/
theorem cutPrefixEdges_reverse_pairwise {n : Nat} (ring : DirectedRing n)
    (b R : Fin n) :
    (cutPrefixEdges ring b R).reverse.Pairwise (fun e f =>
      ring.rightNeighbor e ≠ f ∧
        ring.rightNeighbor e ≠ ring.rightNeighbor f) := by
  apply List.Pairwise.sublist
    ((List.take_sublist (cutCoord ring b R).val
      (cutPathEdges ring b)).reverse)
  exact cutPathEdges_reverse_pairwise ring b

/-- The protected suffix from `R` through the barrier tail is mark-free. -/
def ProtectedSuffix {n k : Nat} (ring : DirectedRing n)
    (C : Fin n → State k) (b R : Fin n) : Prop :=
  ∀ i : Fin n,
    (cutCoord ring b R).val ≤ (cutCoord ring b i).val → MarkFree (C i)

/-- Corridor A retains its chosen survivor, protects the suffix behind it,
and leaves no possible leader except that survivor and the barrier head. -/
structure CorridorAResult {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k)
    (b R : Fin n) : Prop where
  barrier : OneBarrierAt hk ring C b
  survivor : (C R).leader = true
  suffixFresh : ProtectedSuffix ring C b R
  leaders : ∀ i : Fin n, (C i).leader = true →
    i = R ∨ i = ring.rightNeighbor b

theorem rightmost_head_is_unique {n k : Nat} (ring : DirectedRing n)
    (C : Fin n → State k) (b : Fin n)
    (hR : RightmostLeader ring C b (ring.rightNeighbor b)) :
    ∀ i : Fin n, (C i).leader = true → i = ring.rightNeighbor b := by
  intro i hi
  have hle := hR.2 i hi
  have hz : (cutCoord ring b (ring.rightNeighbor b)).val = 0 := by
    have h := cutCoord_cutPos ring b (⟨0, ring.hn⟩ : Fin n)
    simpa using congrArg Fin.val h
  rw [hz] at hle
  have hc : cutCoord ring b i = ⟨0, ring.hn⟩ := by
    apply Fin.ext
    exact Nat.eq_zero_of_le_zero hle
  rw [← cutPos_cutCoord ring b i, hc, cutPos_zero]

theorem protectedSuffix_of_prepared {n k : Nat} (ring : DirectedRing n)
    (C : Fin n → State k) (b R : Fin n)
    (hprepared : PreparedAt ring C b)
    (hR : R ≠ ring.rightNeighbor b) :
    ProtectedSuffix ring C b R := by
  intro i hri
  apply hprepared i
  intro hi
  have hz : (cutCoord ring b i).val = 0 := by
    subst i
    have h := cutCoord_cutPos ring b (⟨0, ring.hn⟩ : Fin n)
    simpa using congrArg Fin.val h
  have hrzero : (cutCoord ring b R).val = 0 := by omega
  apply hR
  rw [← cutPos_cutCoord ring b R]
  have hc : cutCoord ring b R = ⟨0, ring.hn⟩ := by
    apply Fin.ext
    exact hrzero
  rw [hc, cutPos_zero]

/-- If the only possible second survivor at the barrier head is absent,
Corridor A already gives the repository's exact `Clean`. -/
theorem corridorA_clean_of_head_follower {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (b R : Fin n)
    (hA : CorridorAResult hk ring C b R)
    (hhead : (C (ring.rightNeighbor b)).leader = false) :
    Clean hk ring C := by
  refine ⟨R, b, hA.barrier, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [cutView] using hA.survivor
  · intro i hi
    have hphys : (C (cutPos ring b i)).leader = true := by
      simpa [cutView] using hi
    rcases hA.leaders _ hphys with hR | hh
    · apply cutPos_injective ring b
      simpa using hR
    · have : (C (ring.rightNeighbor b)).leader = true := by
        rw [← hh]
        exact hphys
      exact False.elim (Bool.noConfusion (hhead.symm.trans this))
  · intro i hmark
    by_cases hlt : i.val < (cutCoord ring b R).val
    · exact hlt
    · have hfree := hA.suffixFresh (cutPos ring b i) (by
        simpa using (Nat.le_of_not_gt hlt))
      rcases hmark with hb | hp
      · change (C (cutPos ring b i)).bullet = true at hb
        exact False.elim (Bool.noConfusion (hfree.1.symm.trans hb))
      · change (C (cutPos ring b i)).probe = true at hp
        exact False.elim (Bool.noConfusion (hfree.2.symm.trans hp))

/-- One ordinary hit into a bullet-free leader fires the leader's bullet onto
the initiator, clears the initiator probe, and leaves the responder unchanged. -/
theorem step_fire_into_leader {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)))
    (hleader : (C (ring.rightNeighbor e)).leader = true)
    (hbullet : (C (ring.rightNeighbor e)).bullet = false) :
    (step hk ring C e e).bullet = true ∧
      (step hk ring C e e).probe = false ∧
      step hk ring C e (ring.rightNeighbor e) = C (ring.rightNeighbor e) := by
  have htrans : CenteredRenewal.transition hk (C e)
      (C (ring.rightNeighbor e)) =
        ({ C e with bullet := true, probe := false },
          C (ring.rightNeighbor e)) := by
    rw [CenteredRenewal.transition_of_nonbarrier hk _ _ hbar]
    simp [nonBarrierStep, hleader, hbullet]
  have hre := rightNeighbor_ne_self ring hn2 e
  simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans, hre]

/-- A non-head rightmost leader in a prepared cut comes with the exact
protected suffix needed by Corridor A. -/
theorem prepared_rightmost_nonhead {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (b R : Fin n)
    (hone : OneBarrierAt hk ring C b)
    (hprepared : PreparedAt ring C b)
    (hR : RightmostLeader ring C b R)
    (hnonhead : R ≠ ring.rightNeighbor b) :
    OneBarrierAt hk ring C b ∧
      (C R).leader = true ∧
      ProtectedSuffix ring C b R ∧
      (∀ i : Fin n, (C i).leader = true →
        (cutCoord ring b i).val ≤ (cutCoord ring b R).val) := by
  exact ⟨hone, hR.1, protectedSuffix_of_prepared ring C b R hprepared
    hnonhead, hR.2⟩

theorem cutCoord_rightNeighbor_of_not_tail {n : Nat} (ring : DirectedRing n)
    (b i : Fin n) (hi : cutCoord ring b i ≠ tailCoord ring) :
    (cutCoord ring b (ring.rightNeighbor i)).val =
      (cutCoord ring b i).val + 1 := by
  let c := cutCoord ring b i
  have hc : c ≠ tailCoord ring := hi
  have hval := rightNeighbor_val_of_ne_tail ring c hc
  have hphys : ring.rightNeighbor i =
      cutPos ring b (ring.rightNeighbor c) := by
    rw [← cutPos_cutCoord ring b i]
    exact (cutPos_rightNeighbor ring b c).symm
  rw [hphys, cutCoord_cutPos]
  exact hval

theorem cutCoord_leftNeighbor_of_pos {n : Nat} (ring : DirectedRing n)
    (b i : Fin n) (hi : 0 < (cutCoord ring b i).val) :
    (cutCoord ring b (ring.leftNeighbor i)).val + 1 =
      (cutCoord ring b i).val := by
  let c := cutCoord ring b i
  have hval := leftNeighbor_val_of_pos ring c hi
  have hphys : ring.leftNeighbor i = cutPos ring b (ring.leftNeighbor c) := by
    apply rightNeighbor_injective ring
    rw [rightNeighbor_leftNeighbor_clean, ← cutPos_rightNeighbor,
      rightNeighbor_leftNeighbor_clean, cutPos_cutCoord]
  rw [hphys, cutCoord_cutPos]
  change (ring.leftNeighbor c).val + 1 = c.val
  omega

/-- Rank geometry for a non-wrapping forward edge walk. -/
theorem forwardEdgeWalk_succ_geometry {n : Nat} (ring : DirectedRing n)
    (b e : Fin n) (m : Nat)
    (hfit : (cutCoord ring b e).val + (m + 1) < n) :
    let w := forwardEdgeWalk ring e (m + 1)
    (∀ q ∈ w, (cutCoord ring b q).val <
        (cutCoord ring b e).val + (m + 1) ∧
      (cutCoord ring b (ring.rightNeighbor q)).val =
        (cutCoord ring b q).val + 1) ∧
      (cutCoord ring b
        (ring.rightNeighbor (w.getLast (by
          intro hw
          have hlen := forwardEdgeWalk_length ring e (m + 1)
          have hw' : forwardEdgeWalk ring e (m + 1) = [] := by
            simpa [w] using hw
          rw [hw'] at hlen
          simp at hlen)))).val =
        (cutCoord ring b e).val + (m + 1) := by
  induction m generalizing e with
  | zero =>
      have heNotTail : cutCoord ring b e ≠ tailCoord ring := by
        intro htail
        have hv := congrArg Fin.val htail
        change (cutCoord ring b e).val = n - 1 at hv
        omega
      have her := cutCoord_rightNeighbor_of_not_tail ring b e heNotTail
      simp [forwardEdgeWalk, her]
  | succ m ih =>
      have heNotTail : cutCoord ring b e ≠ tailCoord ring := by
        intro htail
        have hv := congrArg Fin.val htail
        change (cutCoord ring b e).val = n - 1 at hv
        omega
      have her := cutCoord_rightNeighbor_of_not_tail ring b e heNotTail
      have htailFit :
          (cutCoord ring b (ring.rightNeighbor e)).val + (m + 1) < n := by
        omega
      have hrec := ih (ring.rightNeighbor e) htailFit
      change
        (∀ q ∈ e :: forwardEdgeWalk ring (ring.rightNeighbor e) (m + 1),
          (cutCoord ring b q).val <
              (cutCoord ring b e).val + (m + 1 + 1) ∧
            (cutCoord ring b (ring.rightNeighbor q)).val =
              (cutCoord ring b q).val + 1) ∧ _
      constructor
      · intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact ⟨by omega, her⟩
        · have hqrec := hrec.1 q hq
          exact ⟨by omega, hqrec.2⟩
      · change (cutCoord ring b (ring.rightNeighbor
            ((e :: forwardEdgeWalk ring (ring.rightNeighbor e) (m + 1)).getLast
              (by simp)))).val =
          (cutCoord ring b e).val + (m + 1 + 1)
        have hlast :
            (e :: forwardEdgeWalk ring (ring.rightNeighbor e) (m + 1)).getLast
                (by simp) =
              (forwardEdgeWalk ring (ring.rightNeighbor e) (m + 1)).getLast
                (by
                  intro hw
                  have hlen := forwardEdgeWalk_length ring
                    (ring.rightNeighbor e) (m + 1)
                  rw [hw] at hlen
                  simp at hlen) := by
          change (e :: ring.rightNeighbor e ::
              forwardEdgeWalk ring (ring.rightNeighbor (ring.rightNeighbor e))
                m).getLast _ =
            (ring.rightNeighbor e ::
              forwardEdgeWalk ring (ring.rightNeighbor (ring.rightNeighbor e))
                m).getLast _
          rfl
        rw [hlast, hrec.2]
        omega

@[simp] theorem cutCoord_barrier {n : Nat} (ring : DirectedRing n)
    (b : Fin n) : cutCoord ring b b = tailCoord ring := by
  apply cutPos_injective ring b
  rw [cutPos_cutCoord, cutPos_tailCoord]

theorem backwardEdgeWalk_rank_le {n : Nat} (ring : DirectedRing n)
    (b e q : Fin n) (m : Nat)
    (hm : m ≤ (cutCoord ring b e).val + 1)
    (hq : q ∈ backwardEdgeWalk ring e m) :
    (cutCoord ring b q).val ≤ (cutCoord ring b e).val := by
  induction m generalizing e with
  | zero => simp [backwardEdgeWalk] at hq
  | succ m ih =>
      simp only [backwardEdgeWalk, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact Nat.le_refl _
      · have hmlen := List.length_pos_of_mem hq
        rw [backwardEdgeWalk_length] at hmlen
        have hepos : 0 < (cutCoord ring b e).val := by omega
        have hleft := cutCoord_leftNeighbor_of_pos ring b e hepos
        have hm' : m ≤ (cutCoord ring b (ring.leftNeighbor e)).val + 1 := by
          omega
        have ihq := ih (ring.leftNeighbor e) hm' hq
        omega

theorem backwardEdgeWalk_reverse_pairwise {n : Nat} (ring : DirectedRing n)
    (b e : Fin n) (m : Nat)
    (hm : m ≤ (cutCoord ring b e).val + 1)
    (hetail : cutCoord ring b e ≠ tailCoord ring) :
    (backwardEdgeWalk ring e m).Pairwise (fun x y =>
      ring.rightNeighbor x ≠ y ∧
        ring.rightNeighbor x ≠ ring.rightNeighbor y) := by
  induction m generalizing e with
  | zero => simp [backwardEdgeWalk]
  | succ m ih =>
      by_cases hm0 : m = 0
      · subst m
        simp [backwardEdgeWalk]
      have hepos : 0 < (cutCoord ring b e).val := by omega
      simp only [backwardEdgeWalk, List.pairwise_cons]
      refine ⟨?_, ?_⟩
      · intro q hq
        have hleft := cutCoord_leftNeighbor_of_pos ring b e hepos
        have hqle := backwardEdgeWalk_rank_le ring b (ring.leftNeighbor e) q m
          (by omega) hq
        have her := cutCoord_rightNeighbor_of_not_tail ring b e hetail
        have hqnotTail : cutCoord ring b q ≠ tailCoord ring := by
          intro hqt
          have hv := congrArg Fin.val hqt
          change (cutCoord ring b q).val = n - 1 at hv
          have heLt := (cutCoord ring b e).isLt
          omega
        have hqr := cutCoord_rightNeighbor_of_not_tail ring b q hqnotTail
        constructor
        · intro heq
          have hv := congrArg (fun z => (cutCoord ring b z).val) heq
          omega
        · intro heq
          have hv := congrArg (fun z => (cutCoord ring b z).val) heq
          omega
      · have hleft := cutCoord_leftNeighbor_of_pos ring b e hepos
        have hleftNotTail :
            cutCoord ring b (ring.leftNeighbor e) ≠ tailCoord ring := by
          intro hbad
          have hv := congrArg Fin.val hbad
          change (cutCoord ring b (ring.leftNeighbor e)).val = n - 1 at hv
          have heLt := (cutCoord ring b e).isLt
          omega
        exact ih (ring.leftNeighbor e) (by omega) hleftNotTail

theorem backwardEdgeWalk_mem_of_rank {n : Nat} (ring : DirectedRing n)
    (b e q : Fin n) (m : Nat)
    (hqle : (cutCoord ring b q).val ≤ (cutCoord ring b e).val)
    (hdist : (cutCoord ring b e).val - (cutCoord ring b q).val < m) :
    q ∈ backwardEdgeWalk ring e m := by
  induction m generalizing e with
  | zero => omega
  | succ m ih =>
      simp only [backwardEdgeWalk, List.mem_cons]
      by_cases hrank : (cutCoord ring b q).val = (cutCoord ring b e).val
      · left
        rw [← cutPos_cutCoord ring b q, ← cutPos_cutCoord ring b e]
        congr 1
        apply Fin.ext
        exact hrank
      · right
        have hepos : 0 < (cutCoord ring b e).val := by omega
        have hleft := cutCoord_leftNeighbor_of_pos ring b e hepos
        apply ih (ring.leftNeighbor e)
        · omega
        · omega

/-- Every positive-rank site up to the start edge is the responder of a
backward walk edge. -/
theorem exists_backwardEdgeWalk_responder {n : Nat} (ring : DirectedRing n)
    (b e i : Fin n) (m : Nat)
    (hipos : 0 < (cutCoord ring b i).val)
    (hile : (cutCoord ring b i).val ≤ (cutCoord ring b e).val + 1)
    (hdist : (cutCoord ring b e).val + 1 -
      (cutCoord ring b i).val < m) :
    ∃ q ∈ backwardEdgeWalk ring e m, ring.rightNeighbor q = i := by
  let q := ring.leftNeighbor i
  have hqrank := cutCoord_leftNeighbor_of_pos ring b i hipos
  change (cutCoord ring b q).val + 1 = (cutCoord ring b i).val at hqrank
  refine ⟨q, ?_, rightNeighbor_leftNeighbor_clean ring i⟩
  apply backwardEdgeWalk_mem_of_rank ring b e q m
  · omega
  · omega

theorem runWord_duplicateEdges_no_leader_birth {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n) (w : List (Fin n))
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b)
    (hordinary : ∀ e ∈ w, e ≠ b) :
    let D := runWord hk ring C (duplicateEdges w)
    OneBarrierAt hk ring D b ∧
      ∀ i : Fin n, (D i).leader = true → (C i).leader = true := by
  induction w generalizing C with
  | nil => simp [hone]
  | cons e w ih =>
      have he : e ≠ b := hordinary e (by simp)
      have hw : ∀ f ∈ w, f ≠ b := by
        intro f hf
        exact hordinary f (by simp [hf])
      have hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
        intro h
        apply he
        exact (hone e).1 ((barrierAt_labelsOf_iff hk ring C e).2 h)
      have honeE := doubleHit_parks_unique_barrier hk ring hn2 C b e hndvd
        hone he
      have hrec := ih (doubleHit hk ring C e) honeE hw
      rw [runWord_duplicateEdges_cons]
      refine ⟨hrec.1, ?_⟩
      intro i hi
      exact doubleHit_no_leader_birth_of_nonbarrier hk ring hn2 C e hbar i
        (hrec.2 i hi)

/-- Explicit Corridor A word from a non-head rightmost leader. -/
def corridorAWord {n : Nat} (ring : DirectedRing n)
    (b R : Fin n) : List (Fin n) :=
  let e := ring.leftNeighbor R
  let back := backwardEdgeWalk ring (ring.leftNeighbor e)
    ((cutCoord ring b R).val - 1)
  e :: duplicateEdges back

theorem corridorAWord_length {n : Nat} (ring : DirectedRing n)
    (b R : Fin n) :
    (corridorAWord ring b R).length =
      1 + 2 * ((cutCoord ring b R).val - 1) := by
  simp [corridorAWord, duplicateEdges_length]
  omega

/-- Corridor A is bounded by `2n-3`; this arithmetic fact is independent of
the protocol state. -/
theorem corridorAWord_length_le {n : Nat} (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (b R : Fin n) :
    (corridorAWord ring b R).length ≤ 2 * n - 3 := by
  rw [corridorAWord_length]
  have hr := (cutCoord ring b R).isLt
  omega

/-- A non-head site has positive cut rank. -/
theorem cutCoord_pos_of_ne_head {n : Nat} (ring : DirectedRing n)
    (b i : Fin n) (hi : i ≠ ring.rightNeighbor b) :
    0 < (cutCoord ring b i).val := by
  apply Nat.pos_of_ne_zero
  intro hz
  apply hi
  rw [← cutPos_cutCoord ring b i]
  have hc : cutCoord ring b i = (⟨0, ring.hn⟩ : Fin n) := by
    apply Fin.ext
    exact hz
  rw [hc, cutPos_zero]

/-- The doubled part of Corridor A visits exactly the positive-rank sites
strictly before its selected survivor as responders.  Its edges are ordinary
and satisfy the reverse frame relation required by the tracked-bullet lemma. -/
theorem corridorA_back_geometry {n : Nat} (ring : DirectedRing n)
    (b R : Fin n) (hnonhead : R ≠ ring.rightNeighbor b) :
    let r := (cutCoord ring b R).val
    let e := ring.leftNeighbor R
    let backStart := ring.leftNeighbor e
    let back := backwardEdgeWalk ring backStart (r - 1)
    BackwardBulletChain ring back ∧
      back.Pairwise (fun x y => ring.rightNeighbor x ≠ y ∧
        ring.rightNeighbor x ≠ ring.rightNeighbor y) ∧
      (∀ q ∈ back, q ≠ b) ∧
      (∀ q ∈ back, (cutCoord ring b q).val < r ∧
        (cutCoord ring b (ring.rightNeighbor q)).val < r) ∧
      (∀ i : Fin n, 0 < (cutCoord ring b i).val →
        (cutCoord ring b i).val < r →
        ∃ q ∈ back, ring.rightNeighbor q = i) := by
  let r := (cutCoord ring b R).val
  let e := ring.leftNeighbor R
  let backStart := ring.leftNeighbor e
  let back := backwardEdgeWalk ring backStart (r - 1)
  change BackwardBulletChain ring back ∧
    back.Pairwise (fun x y => ring.rightNeighbor x ≠ y ∧
      ring.rightNeighbor x ≠ ring.rightNeighbor y) ∧
    (∀ q ∈ back, q ≠ b) ∧
    (∀ q ∈ back, (cutCoord ring b q).val < r ∧
      (cutCoord ring b (ring.rightNeighbor q)).val < r) ∧
    (∀ i : Fin n, 0 < (cutCoord ring b i).val →
      (cutCoord ring b i).val < r →
      ∃ q ∈ back, ring.rightNeighbor q = i)
  have hrpos : 0 < r := cutCoord_pos_of_ne_head ring b R hnonhead
  have heRank := cutCoord_leftNeighbor_of_pos ring b R hrpos
  change (cutCoord ring b e).val + 1 = r at heRank
  by_cases hrone : r = 1
  · have hrsub : r - 1 = 0 := by omega
    have hback : back = [] := by simp [back, hrsub, backwardEdgeWalk]
    rw [hback]
    refine ⟨trivial, .nil, ?_, ?_, ?_⟩
    · simp
    · simp
    · intro i _hiPos hiLt
      omega
  · have hepos : 0 < (cutCoord ring b e).val := by omega
    have hbackRank := cutCoord_leftNeighbor_of_pos ring b e hepos
    change (cutCoord ring b backStart).val + 1 =
      (cutCoord ring b e).val at hbackRank
    have hbackNotTail : cutCoord ring b backStart ≠ tailCoord ring := by
      intro htail
      have hv := congrArg Fin.val htail
      change (cutCoord ring b backStart).val = n - 1 at hv
      have hrlt := (cutCoord ring b R).isLt
      omega
    have hlen : r - 1 ≤ (cutCoord ring b backStart).val + 1 := by omega
    refine ⟨backwardEdgeWalk_chain ring backStart (r - 1), ?_, ?_, ?_, ?_⟩
    · exact backwardEdgeWalk_reverse_pairwise ring b backStart (r - 1)
        hlen hbackNotTail
    · intro q hq hqb
      have hqle := backwardEdgeWalk_rank_le ring b backStart q (r - 1)
        hlen hq
      subst q
      have hbRank : (cutCoord ring b b).val = n - 1 := by
        simp [tailCoord]
      have hrlt := (cutCoord ring b R).isLt
      omega
    · intro q hq
      have hqle := backwardEdgeWalk_rank_le ring b backStart q (r - 1)
        hlen hq
      have hqNotTail : cutCoord ring b q ≠ tailCoord ring := by
        intro htail
        have hv := congrArg Fin.val htail
        change (cutCoord ring b q).val = n - 1 at hv
        have hrlt := (cutCoord ring b R).isLt
        omega
      have hqr := cutCoord_rightNeighbor_of_not_tail ring b q hqNotTail
      constructor <;> omega
    · intro i hiPos hiLt
      apply exists_backwardEdgeWalk_responder ring b backStart i (r - 1)
      · exact hiPos
      · omega
      · omega

theorem backwardEdgeWalk_head {n : Nat} (ring : DirectedRing n)
    (e : Fin n) (m : Nat) (hm : 0 < m) :
    (backwardEdgeWalk ring e m).head (by
      intro h
      have hlen := backwardEdgeWalk_length ring e m
      rw [h] at hlen
      simp at hlen
      omega) = e := by
  cases m with
  | zero => omega
  | succ m => rfl

/-- Corridor A fires the selected rightmost leader and sweeps its tracked
bullet back to the cut head.  The selected leader and its prepared suffix are
framed, while every other surviving leader can only be the barrier head. -/
theorem corridorA_reaches_result {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b R : Fin n) (hndvd : ¬ k ∣ n)
    (hone : OneBarrierAt hk ring C b)
    (hprepared : PreparedAt ring C b)
    (hR : RightmostLeader ring C b R)
    (hnonhead : R ≠ ring.rightNeighbor b) :
    let w := corridorAWord ring b R
    let D := runWord hk ring C w
    w.length ≤ 2 * n - 3 ∧ CorridorAResult hk ring D b R := by
  have hn2 : 1 < n := by omega
  let r := (cutCoord ring b R).val
  let e := ring.leftNeighbor R
  let backStart := ring.leftNeighbor e
  let back := backwardEdgeWalk ring backStart (r - 1)
  let F := step hk ring C e
  let D := runWord hk ring F (duplicateEdges back)
  have hrpos : 0 < r := cutCoord_pos_of_ne_head ring b R hnonhead
  have heRank := cutCoord_leftNeighbor_of_pos ring b R hrpos
  change (cutCoord ring b e).val + 1 = r at heRank
  have her : ring.rightNeighbor e = R := rightNeighbor_leftNeighbor_clean ring R
  have heOrd : e ≠ b := by
    intro heb
    apply hnonhead
    rw [← her, heb]
  have hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
    intro h
    apply heOrd
    exact (hone e).1 ((barrierAt_labelsOf_iff hk ring C e).2 h)
  have hsuffix := protectedSuffix_of_prepared ring C b R hprepared hnonhead
  have hfire := step_fire_into_leader hk ring hn2 C e hbar (by
    rw [her]
    exact hR.1) (by
    rw [her]
    exact (hsuffix R (Nat.le_refl _)).1)
  have hnot : ¬ CenteredRenewal.AdvanceReady hk ring C e := by
    intro hready
    exact hbar hready.1
  have honeF0 := oneBarrier_step hk ring hn2 C b e hndvd hone
  have honeF : OneBarrierAt hk ring F b := by
    simpa [F, hnot] using honeF0
  have hgeom := corridorA_back_geometry ring b R hnonhead
  have hchain : BackwardBulletChain ring back := by
    simpa [back, backStart, e, r] using hgeom.1
  have hpair : back.Pairwise (fun x y =>
      ring.rightNeighbor x ≠ y ∧
        ring.rightNeighbor x ≠ ring.rightNeighbor y) := by
    simpa [back, backStart, e, r] using hgeom.2.1
  have hord : ∀ q ∈ back, q ≠ b := by
    simpa [back, backStart, e, r] using hgeom.2.2.1
  have hranks : ∀ q ∈ back, (cutCoord ring b q).val < r ∧
      (cutCoord ring b (ring.rightNeighbor q)).val < r := by
    simpa [back, backStart, e, r] using hgeom.2.2.2.1
  have hcoverage : ∀ i : Fin n, 0 < (cutCoord ring b i).val →
      (cutCoord ring b i).val < r →
      ∃ q ∈ back, ring.rightNeighbor q = i := by
    simpa [back, backStart, e, r] using hgeom.2.2.2.2
  have honeD : OneBarrierAt hk ring D b := by
    exact runWord_duplicateEdges_parks_unique_barrier hk ring hn2 F b back
      hndvd honeF hord
  have hnobirth := runWord_duplicateEdges_no_leader_birth hk ring hn2 F b back
    hndvd honeF hord
  have hsuffixFrame : ∀ i : Fin n, r ≤ (cutCoord ring b i).val →
      D i = C i := by
    intro i hirank
    have hFi : F i = C i := by
      by_cases hiR : i = R
      · subst i
        rw [← her]
        exact hfire.2.2
      · have hie : i ≠ e := by
          intro hie
          subst i
          omega
        simp [F, step, PopulationProtocol.step, hie, her, hiR]
    change runWord hk ring F (duplicateEdges back) i = C i
    rw [runWord_duplicateEdges_frame hk ring F back i]
    · exact hFi
    · intro q hq
      have hqr := hranks q hq
      constructor
      · intro hiq
        subst i
        omega
      · intro hiq
        subst i
        omega
  have hsurvivor : (D R).leader = true := by
    rw [hsuffixFrame R (Nat.le_refl _)]
    exact hR.1
  have hleaders : ∀ i : Fin n, (D i).leader = true →
      i = R ∨ i = ring.rightNeighbor b := by
    intro i hiD
    have hiF := hnobirth.2 i hiD
    have hiC := step_no_leader_birth_of_nonbarrier hk ring hn2 C e hbar i hiF
    by_cases hiRphys : i = R
    · exact Or.inl hiRphys
    have hirLe : (cutCoord ring b i).val ≤ r := hR.2 i hiC
    have hirLt : (cutCoord ring b i).val < r := by
      by_cases heq : (cutCoord ring b i).val = r
      · apply False.elim
        apply hiRphys
        rw [← cutPos_cutCoord ring b i, ← cutPos_cutCoord ring b R]
        congr 1
        apply Fin.ext
        exact heq
      · omega
    by_cases hizero : (cutCoord ring b i).val = 0
    · right
      rw [← cutPos_cutCoord ring b i]
      have hc : cutCoord ring b i = (⟨0, ring.hn⟩ : Fin n) := by
        apply Fin.ext
        exact hizero
      rw [hc, cutPos_zero]
    · have hipos : 0 < (cutCoord ring b i).val := Nat.pos_of_ne_zero hizero
      obtain ⟨q, hq, hqi⟩ := hcoverage i hipos hirLt
      have hne : back ≠ [] := by
        intro hempty
        rw [hempty] at hq
        simp at hq
      have hfirst : back.head hne = backStart := by
        have hmlen : 0 < r - 1 := by
          have hlen := List.length_pos_of_mem hq
          rw [backwardEdgeWalk_length] at hlen
          simpa [back, backStart, e] using hlen
        simpa [back] using backwardEdgeWalk_head ring backStart (r - 1) hmlen
      cases hback : back with
      | nil => exact False.elim (hne hback)
      | cons q0 rest =>
        have hbullet : (F (ring.rightNeighbor q0)).bullet = true := by
          have hhead : q0 = backStart := by
            simpa [hback] using hfirst
          rw [hhead, rightNeighbor_leftNeighbor_clean]
          exact hfire.1
        have htrack := runWord_duplicateEdges_tracks_bullet hk ring hn2 F b
          q0 rest hndvd honeF (by simpa [hback] using hord)
          (by simpa [hback] using hpair) (by simpa [hback] using hchain)
          hbullet
        have hkilled := htrack.2.2 q (by simpa [hback] using hq)
        rw [hqi] at hkilled
        have hiD' :
            (runWord hk ring F (duplicateEdges (q0 :: rest)) i).leader =
              true := by
          simpa [D, hback] using hiD
        exact False.elim (Bool.noConfusion (hkilled.symm.trans hiD'))
  refine ⟨corridorAWord_length_le ring hn3 b R, ?_⟩
  have hresult : CorridorAResult hk ring D b R := by
    refine ⟨honeD, hsurvivor, ?_, hleaders⟩
    intro i hi
    rw [hsuffixFrame i hi]
    exact hsuffix i hi
  simpa [corridorAWord, D, F, back, backStart, e, r, runWord_cons] using hresult

theorem corridorA_no_leader_birth {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b R : Fin n) (hndvd : ¬ k ∣ n)
    (hone : OneBarrierAt hk ring C b)
    (hnonhead : R ≠ ring.rightNeighbor b) :
    ∀ i : Fin n,
      (runWord hk ring C (corridorAWord ring b R) i).leader = true →
        (C i).leader = true := by
  let r := (cutCoord ring b R).val
  let e := ring.leftNeighbor R
  let back := backwardEdgeWalk ring (ring.leftNeighbor e) (r - 1)
  let F := step hk ring C e
  have heOrd : e ≠ b := by
    intro heb
    apply hnonhead
    have heb' : ring.leftNeighbor R = b := by simpa [e] using heb
    rw [← rightNeighbor_leftNeighbor_clean ring R, heb']
  have hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
    intro h
    apply heOrd
    exact (hone e).1 ((barrierAt_labelsOf_iff hk ring C e).2 h)
  have hnot : ¬ CenteredRenewal.AdvanceReady hk ring C e := by
    intro hready
    exact hbar hready.1
  have honeF0 := oneBarrier_step hk ring hn2 C b e hndvd hone
  have honeF : OneBarrierAt hk ring F b := by simpa [F, hnot] using honeF0
  have hgeom := corridorA_back_geometry ring b R hnonhead
  have hord : ∀ q ∈ back, q ≠ b := by
    simpa [back, e, r] using hgeom.2.2.1
  have hnobirth := runWord_duplicateEdges_no_leader_birth hk ring hn2 F b back
    hndvd honeF hord
  intro i hi
  have hiF : (F i).leader = true := by
    apply hnobirth.2 i
    simpa [corridorAWord, F, back, e, r, runWord_cons] using hi
  exact step_no_leader_birth_of_nonbarrier hk ring hn2 C e hbar i hiF

/-- The terminal tail-survivor word: fire the tail once from its incoming
ordinary edge, then carry that bullet backward through all remaining ordinary
edges except the barrier head's incoming barrier. -/
def finalCorridorWord {n : Nat} (ring : DirectedRing n) (b : Fin n) :
    List (Fin n) :=
  let e := ring.leftNeighbor b
  e :: duplicateEdges
    (backwardEdgeWalk ring (ring.leftNeighbor e) (n - 2))

theorem finalCorridorWord_length {n : Nat} (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (b : Fin n) :
    (finalCorridorWord ring b).length = 2 * n - 3 := by
  simp [finalCorridorWord, duplicateEdges_length]
  omega

/-- The doubled suffix of the terminal word has exactly the geometry required
by the tracked-bullet induction. -/
theorem finalCorridor_back_geometry {n : Nat} (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (b : Fin n) :
    let e := ring.leftNeighbor (ring.leftNeighbor b)
    let w := backwardEdgeWalk ring e (n - 2)
    w ≠ [] ∧ BackwardBulletChain ring w ∧
      w.Pairwise (fun x y => ring.rightNeighbor x ≠ y ∧
        ring.rightNeighbor x ≠ ring.rightNeighbor y) ∧
      (∀ q ∈ w, q ≠ b) := by
  let e := ring.leftNeighbor (ring.leftNeighbor b)
  have hbRank : (cutCoord ring b b).val = n - 1 := by
    simp [tailCoord]
  have hbpos : 0 < (cutCoord ring b b).val := by omega
  have hleft1 := cutCoord_leftNeighbor_of_pos ring b b hbpos
  change (cutCoord ring b (ring.leftNeighbor b)).val + 1 =
    (cutCoord ring b b).val at hleft1
  have hleftpos : 0 < (cutCoord ring b (ring.leftNeighbor b)).val := by omega
  have heRank := cutCoord_leftNeighbor_of_pos ring b (ring.leftNeighbor b)
    hleftpos
  change (cutCoord ring b e).val + 1 =
    (cutCoord ring b (ring.leftNeighbor b)).val at heRank
  have heNotTail : cutCoord ring b e ≠ tailCoord ring := by
    intro h
    have hv := congrArg Fin.val h
    change (cutCoord ring b e).val = n - 1 at hv
    omega
  refine ⟨?_, backwardEdgeWalk_chain ring e (n - 2), ?_, ?_⟩
  · intro hempty
    have hlen := backwardEdgeWalk_length ring e (n - 2)
    rw [hempty] at hlen
    simp at hlen
    omega
  · apply backwardEdgeWalk_reverse_pairwise ring b e (n - 2)
      (by omega) heNotTail
  · intro q hq hqb
    subst q
    have hqle := backwardEdgeWalk_rank_le ring b e b (n - 2) (by omega) hq
    omega

/-- Nonempty-list wrapper around the head/tail tracked-bullet induction. -/
theorem runWord_duplicateEdges_tracks_bullet_list {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n) (w : List (Fin n))
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b)
    (hne : w ≠ []) (hordinary : ∀ e ∈ w, e ≠ b)
    (hreverse : w.Pairwise (fun x y => ring.rightNeighbor x ≠ y ∧
      ring.rightNeighbor x ≠ ring.rightNeighbor y))
    (hchain : BackwardBulletChain ring w)
    (hbullet : (C (ring.rightNeighbor (w.head hne))).bullet = true) :
    let D := runWord hk ring C (duplicateEdges w)
    OneBarrierAt hk ring D b ∧
      (∀ e ∈ w, (D (ring.rightNeighbor e)).leader = false) := by
  cases hw : w with
  | nil => exact False.elim (hne hw)
  | cons e rest =>
      have hb : (C (ring.rightNeighbor e)).bullet = true := by
        simpa [hw] using hbullet
      have h := runWord_duplicateEdges_tracks_bullet hk ring hn2 C b e rest
        hndvd hone (by simpa [hw] using hordinary)
        (by simpa [hw] using hreverse) (by simpa [hw] using hchain) hb
      exact ⟨h.1, h.2.2⟩

theorem finalCorridor_back_avoids_tail {n : Nat} (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (b q : Fin n)
    (hq : q ∈ backwardEdgeWalk ring
      (ring.leftNeighbor (ring.leftNeighbor b)) (n - 2)) :
    b ≠ q ∧ b ≠ ring.rightNeighbor q := by
  have hgeom := finalCorridor_back_geometry ring hn3 b
  refine ⟨Ne.symm (hgeom.2.2.2 q hq), ?_⟩
  intro hbq
  have hbRank : (cutCoord ring b b).val = n - 1 := by simp [tailCoord]
  have hbpos : 0 < (cutCoord ring b b).val := by omega
  have hleft1 := cutCoord_leftNeighbor_of_pos ring b b hbpos
  have hleftpos : 0 < (cutCoord ring b (ring.leftNeighbor b)).val := by omega
  have heRank := cutCoord_leftNeighbor_of_pos ring b (ring.leftNeighbor b)
    hleftpos
  have hqle := backwardEdgeWalk_rank_le ring b
    (ring.leftNeighbor (ring.leftNeighbor b)) q (n - 2) (by omega) hq
  have hqNotTail : cutCoord ring b q ≠ tailCoord ring := by
    intro h
    have hv := congrArg Fin.val h
    change (cutCoord ring b q).val = n - 1 at hv
    omega
  have hqr := cutCoord_rightNeighbor_of_not_tail ring b q hqNotTail
  have hv := congrArg (fun z => (cutCoord ring b z).val) hbq
  omega

theorem finalCorridor_tail_frame {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b : Fin n)
    (hready : FinalCorridorReady hk ring C b) :
    runWord hk ring C (finalCorridorWord ring b) b = C b := by
  have hn2 : 1 < n := by omega
  let e := ring.leftNeighbor b
  let back := backwardEdgeWalk ring (ring.leftNeighbor e) (n - 2)
  have her : ring.rightNeighbor e = b := rightNeighbor_leftNeighbor_clean ring b
  have he : e ≠ b := by
    intro h
    have := congrArg (ring.rightNeighbor) h
    rw [her] at this
    exact (rightNeighbor_ne_self ring hn2 b) this.symm
  have hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
    intro h
    apply he
    exact (hready.barrier e).1 ((barrierAt_labelsOf_iff hk ring C e).2 h)
  have hfire := step_fire_into_leader hk ring hn2 C e hbar (by
    rw [her]; exact hready.tailLeader) (by
    rw [her]; exact hready.tailFresh.1)
  rw [finalCorridorWord, runWord_cons]
  change runWord hk ring (step hk ring C e) (duplicateEdges back) b = C b
  rw [runWord_duplicateEdges_frame hk ring (step hk ring C e) back b]
  · rw [← her]
    exact hfire.2.2
  · intro q hq
    simpa [back, e] using finalCorridor_back_avoids_tail ring hn3 b q (by
      simpa [back, e] using hq)

theorem cleanData_of_tail_unique {n k : Nat} (ring : DirectedRing n)
    (D : Fin n → State k) (b : Fin n)
    (hleader : (D b).leader = true)
    (hunique : ∀ i : Fin n, (D i).leader = true → i = b)
    (hfresh : MarkFree (D b)) :
    CleanData (cutView ring b D) (cutCoord ring b b) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [cutView] using hleader
  · intro i hi
    have hp : (D (cutPos ring b i)).leader = true := by
      simpa [cutView] using hi
    have hib := hunique _ hp
    apply cutPos_injective ring b
    rw [cutPos_cutCoord]
    exact hib
  · intro i hm
    rw [cutCoord_barrier]
    change i.val < n - 1
    by_cases hi : i.val < n - 1
    · exact hi
    · have hit : i = tailCoord ring := by
        apply Fin.ext
        simp [tailCoord]
        have hiLt := i.isLt
        omega
      subst i
      rcases hm with hb | hp
      · have hb' : (D b).bullet = true := by simpa [cutView] using hb
        exact False.elim (Bool.noConfusion (hfresh.1.symm.trans hb'))
      · have hp' : (D b).probe = true := by simpa [cutView] using hp
        exact False.elim (Bool.noConfusion (hfresh.2.symm.trans hp'))

theorem finalCorridor_reaches_clean {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b : Fin n) (hndvd : ¬ k ∣ n)
    (hready : FinalCorridorReady hk ring C b) :
    let w := finalCorridorWord ring b
    w.length = 2 * n - 3 ∧ Clean hk ring (runWord hk ring C w) := by
  have hn2 : 1 < n := by omega
  let e := ring.leftNeighbor b
  let backStart := ring.leftNeighbor e
  let back := backwardEdgeWalk ring backStart (n - 2)
  let F := step hk ring C e
  let D := runWord hk ring F (duplicateEdges back)
  have her : ring.rightNeighbor e = b := rightNeighbor_leftNeighbor_clean ring b
  have he : e ≠ b := by
    intro h
    have hh := congrArg (ring.rightNeighbor) h
    rw [her] at hh
    exact (rightNeighbor_ne_self ring hn2 b) hh.symm
  have hbar : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
    intro h
    apply he
    exact (hready.barrier e).1 ((barrierAt_labelsOf_iff hk ring C e).2 h)
  have hfire := step_fire_into_leader hk ring hn2 C e hbar (by
    rw [her]; exact hready.tailLeader) (by
    rw [her]; exact hready.tailFresh.1)
  have hnot : ¬ CenteredRenewal.AdvanceReady hk ring C e := by
    intro h
    exact hbar h.1
  have honeF0 := oneBarrier_step hk ring hn2 C b e hndvd hready.barrier
  have honeF : OneBarrierAt hk ring F b := by simpa [F, hnot] using honeF0
  have hgeom := finalCorridor_back_geometry ring hn3 b
  have hne : back ≠ [] := by simpa [back, backStart, e] using hgeom.1
  have hord : ∀ q ∈ back, q ≠ b := by
    simpa [back, backStart, e] using hgeom.2.2.2
  have hfirst : back.head hne = backStart := by
    have hnsub : n - 2 = (n - 3) + 1 := by omega
    simp [back, hnsub, backwardEdgeWalk]
  have htrack := runWord_duplicateEdges_tracks_bullet_list hk ring hn2 F b back
    hndvd honeF hne hord (by
      simpa [back, backStart, e] using hgeom.2.2.1) (by
      simpa [back, backStart, e] using hgeom.2.1) (by
      rw [hfirst, rightNeighbor_leftNeighbor_clean]
      exact hfire.1)
  have hnobirth := runWord_duplicateEdges_no_leader_birth hk ring hn2 F b back
    hndvd honeF hord
  have htail := finalCorridor_tail_frame hk ring hn3 C b hready
  have htailD : D b = C b := by
    simpa [finalCorridorWord, D, F, back, backStart, e, runWord_cons] using htail
  have hunique : ∀ x : Fin n, (D x).leader = true → x = b := by
    intro x hx
    by_cases hxb : x = b
    · exact hxb
    have hxF := hnobirth.2 x hx
    have hxC := step_no_leader_birth_of_nonbarrier hk ring hn2 C e hbar x hxF
    have hxrankNeTail : (cutCoord ring b x).val ≠ n - 1 := by
      intro hv
      apply hxb
      rw [← cutPos_cutCoord ring b x]
      have hc : cutCoord ring b x = tailCoord ring := by
        apply Fin.ext
        simpa [tailCoord] using hv
      rw [hc, cutPos_tailCoord]
    by_cases hxzero : (cutCoord ring b x).val = 0
    · have hxhead : x = ring.rightNeighbor b := by
        rw [← cutPos_cutCoord ring b x]
        have hc : cutCoord ring b x = ⟨0, ring.hn⟩ := by
          apply Fin.ext
          exact hxzero
        rw [hc, cutPos_zero]
      rw [hxhead, hready.headFollower] at hxC
      contradiction
    · have hxpos : 0 < (cutCoord ring b x).val := Nat.pos_of_ne_zero hxzero
      have hbackRank : (cutCoord ring b backStart).val = n - 3 := by
        have hbRank : (cutCoord ring b b).val = n - 1 := by simp [tailCoord]
        have hbpos : 0 < (cutCoord ring b b).val := by omega
        have h1 := cutCoord_leftNeighbor_of_pos ring b b hbpos
        change (cutCoord ring b e).val + 1 = (cutCoord ring b b).val at h1
        have hepos : 0 < (cutCoord ring b e).val := by omega
        have h2 := cutCoord_leftNeighbor_of_pos ring b e hepos
        change (cutCoord ring b backStart).val + 1 =
          (cutCoord ring b e).val at h2
        omega
      obtain ⟨q, hq, hqx⟩ := exists_backwardEdgeWalk_responder ring b
        backStart x (n - 2) hxpos (by
          have hxlt := (cutCoord ring b x).isLt
          omega) (by
          omega)
      have hkilled := htrack.2 q hq
      rw [hqx, hx] at hkilled
      contradiction
  have hcleanD : Clean hk ring D := by
    refine ⟨b, b, hnobirth.1, ?_⟩
    apply cleanData_of_tail_unique ring D b
    · rw [htailD]
      exact hready.tailLeader
    · exact hunique
    · rw [htailD]
      exact hready.tailFresh
  refine ⟨finalCorridorWord_length ring hn3 b, ?_⟩
  simpa [finalCorridorWord, D, F, back, backStart, e, runWord_cons] using hcleanD

/-- If the selected rightmost leader is already the barrier head, it is the
unique leader and one centered advance reaches `Clean` in at most two hits. -/
theorem rightmost_head_reaches_clean {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b : Fin n) (hndvd : ¬ k ∣ n)
    (hone : OneBarrierAt hk ring C b) (hprepared : PreparedAt ring C b)
    (hR : RightmostLeader ring C b (ring.rightNeighbor b)) :
    ∃ w : List (Fin n), w.length ≤ 2 ∧
      Clean hk ring (runWord hk ring C w) := by
  have hn2 : 1 < n := by omega
  have htail := hprepared.tail_markFree ring hn2
  let w := advanceOverHeadLeaderWord C b
  let D := runWord hk ring C w
  have hadv := advance_over_head_leader hk ring hn2 C b hndvd hone
    htail.2 hR.1
  refine ⟨w, hadv.1, ?_⟩
  refine ⟨ring.rightNeighbor b, ring.rightNeighbor b, hadv.2.1, ?_⟩
  apply cleanData_of_tail_unique ring D (ring.rightNeighbor b)
  · exact hadv.2.2.1
  · intro i hi
    have hiC : (C i).leader = true := by
      rw [← hadv.2.2.2.2 i]
      exact hi
    exact rightmost_head_is_unique ring C b hR i hiC
  · exact hadv.2.2.2.1

theorem rightNeighbor_sq_ne_self {n : Nat} (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (i : Fin n) :
    ring.rightNeighbor (ring.rightNeighbor i) ≠ i := by
  let p := ring.leftNeighbor i
  have hpi : ring.rightNeighbor p = i := rightNeighbor_leftNeighbor_clean ring i
  have hiRank : (cutCoord ring p i).val = 0 := by
    rw [← hpi]
    have h := cutCoord_cutPos ring p (⟨0, ring.hn⟩ : Fin n)
    simpa using congrArg Fin.val h
  have hiNotTail : cutCoord ring p i ≠ tailCoord ring := by
    intro htail
    have hv := congrArg Fin.val htail
    change (cutCoord ring p i).val = n - 1 at hv
    omega
  have hri := cutCoord_rightNeighbor_of_not_tail ring p i hiNotTail
  have hriNotTail : cutCoord ring p (ring.rightNeighbor i) ≠ tailCoord ring := by
    intro htail
    have hv := congrArg Fin.val htail
    change (cutCoord ring p (ring.rightNeighbor i)).val = n - 1 at hv
    omega
  have hrri := cutCoord_rightNeighbor_of_not_tail ring p
    (ring.rightNeighbor i) hriNotTail
  intro hsq
  have hv := congrArg (fun q => (cutCoord ring p q).val) hsq
  omega

/-- If Corridor A leaves a leader at the barrier head, advancing across one
or two consecutive leader heads reaches the exact endpoint required by the
final corridor.  The second advance is needed only when the selected survivor
was immediately behind the old head. -/
theorem corridorA_head_leader_reaches_ready {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b R : Fin n) (hndvd : ¬ k ∣ n)
    (hA : CorridorAResult hk ring C b R)
    (hhead : (C (ring.rightNeighbor b)).leader = true) :
    ∃ w : List (Fin n), ∃ b' : Fin n,
      w.length ≤ 4 ∧
        FinalCorridorReady hk ring (runWord hk ring C w) b' := by
  have hn2 : 1 < n := by omega
  let b1 := ring.rightNeighbor b
  let w1 := advanceOverHeadLeaderWord C b
  let D1 := runWord hk ring C w1
  have htailProbe : (C b).probe = false := by
    exact (hA.suffixFresh b (by
      have hr := (cutCoord ring b R).isLt
      simp [tailCoord]
      omega)).2
  have hadv1 := advance_over_head_leader hk ring hn2 C b hndvd hA.barrier
    htailProbe hhead
  by_cases hnext : (D1 (ring.rightNeighbor b1)).leader = false
  · refine ⟨w1, b1, ?_, ?_⟩
    · have hw1 : w1.length ≤ 2 := by simpa [w1] using hadv1.1
      omega
    exact ⟨hadv1.2.1, hadv1.2.2.1, hadv1.2.2.2.1, hnext⟩
  · have hnextTrue : (D1 (ring.rightNeighbor b1)).leader = true := by
      cases hval : (D1 (ring.rightNeighbor b1)).leader with
      | false => exact False.elim (hnext hval)
      | true => rfl
    have hnextC : (C (ring.rightNeighbor b1)).leader = true := by
      rw [← hadv1.2.2.2.2]
      exact hnextTrue
    have hRnext : R = ring.rightNeighbor b1 := by
      rcases hA.leaders _ hnextC with hR | hb1
      · exact hR.symm
      · exact False.elim ((rightNeighbor_ne_self ring hn2 b1) hb1)
    let w2 := advanceOverHeadLeaderWord D1 b1
    let D2 := runWord hk ring D1 w2
    have hadv2 := advance_over_head_leader hk ring hn2 D1 b1 hndvd
      hadv1.2.1 hadv1.2.2.2.1.2 hnextTrue
    have hfinalHead : (D2
        (ring.rightNeighbor (ring.rightNeighbor b1))).leader = false := by
      cases hval : (D2
          (ring.rightNeighbor (ring.rightNeighbor b1))).leader with
      | false => rfl
      | true =>
          have hD1 : (D1
              (ring.rightNeighbor (ring.rightNeighbor b1))).leader = true := by
            rw [← hadv2.2.2.2.2]
            exact hval
          have hC : (C
              (ring.rightNeighbor (ring.rightNeighbor b1))).leader = true := by
            rw [← hadv1.2.2.2.2]
            exact hD1
          rcases hA.leaders _ hC with hR | hb1
          · rw [hRnext] at hR
            exact False.elim ((rightNeighbor_ne_self ring hn2
              (ring.rightNeighbor b1)) hR)
          · exact False.elim ((rightNeighbor_sq_ne_self ring hn3 b1) hb1)
    refine ⟨w1 ++ w2, ring.rightNeighbor b1, ?_, ?_⟩
    · rw [List.length_append]
      have hw1 : w1.length ≤ 2 := by simpa [w1] using hadv1.1
      have hw2 : w2.length ≤ 2 := by simpa [w2] using hadv2.1
      omega
    · rw [runWord_append]
      exact ⟨hadv2.2.1, hadv2.2.2.1, hadv2.2.2.2.1, hfinalHead⟩

/-- The non-head rightmost-leader arm consists of Corridor A, at most four
barrier hits to position a fresh leader tail when necessary, and the exact
final corridor. -/
theorem rightmost_nonhead_reaches_clean {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b R : Fin n) (hndvd : ¬ k ∣ n)
    (hone : OneBarrierAt hk ring C b)
    (hprepared : PreparedAt ring C b)
    (hR : RightmostLeader ring C b R)
    (hnonhead : R ≠ ring.rightNeighbor b) :
    ∃ w : List (Fin n), w.length ≤ 4 * n - 2 ∧
      Clean hk ring (runWord hk ring C w) := by
  let wA := corridorAWord ring b R
  let A := runWord hk ring C wA
  have hA := corridorA_reaches_result hk ring hn3 C b R hndvd hone hprepared
    hR hnonhead
  by_cases hhead : (A (ring.rightNeighbor b)).leader = false
  · refine ⟨wA, ?_, ?_⟩
    · have hwA : wA.length ≤ 2 * n - 3 := by simpa [wA] using hA.1
      omega
    · exact corridorA_clean_of_head_follower hk ring A b R hA.2 hhead
  · have hheadTrue : (A (ring.rightNeighbor b)).leader = true := by
      cases hval : (A (ring.rightNeighbor b)).leader with
      | false => exact False.elim (hhead hval)
      | true => rfl
    obtain ⟨wm, b', hwm, hready⟩ :=
      corridorA_head_leader_reaches_ready hk ring hn3 A b R hndvd hA.2
        hheadTrue
    have hfinal := finalCorridor_reaches_clean hk ring hn3
      (runWord hk ring A wm) b' hndvd hready
    refine ⟨wA ++ wm ++ finalCorridorWord ring b', ?_, ?_⟩
    · simp only [List.length_append]
      have hwA : wA.length ≤ 2 * n - 3 := by simpa [wA] using hA.1
      have hwF : (finalCorridorWord ring b').length = 2 * n - 3 := hfinal.1
      omega
    · rw [runWord_append, runWord_append]
      exact hfinal.2

/-- Every prepared one-barrier configuration containing a leader reaches
`Clean` within the common terminal budget. -/
theorem prepared_with_leader_reaches_clean {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b : Fin n) (hndvd : ¬ k ∣ n)
    (hone : OneBarrierAt hk ring C b)
    (hprepared : PreparedAt ring C b)
    (hHas : ∃ i : Fin n, (C i).leader = true) :
    ∃ w : List (Fin n), w.length ≤ 4 * n - 2 ∧
      Clean hk ring (runWord hk ring C w) := by
  obtain ⟨R, hR⟩ := exists_rightmostLeader ring C b hHas
  by_cases hhead : R = ring.rightNeighbor b
  · subst R
    obtain ⟨w, hw, hclean⟩ := rightmost_head_reaches_clean hk ring hn3 C b
      hndvd hone hprepared hR
    exact ⟨w, by omega, hclean⟩
  · exact rightmost_nonhead_reaches_clean hk ring hn3 C b R hndvd hone
      hprepared hR hhead

/-- The zero-leader arm uses a phase-zero barrier hit to seed one probe,
transports that unique probe once around the ordinary cut, and consumes it at
the armed barrier.  This creates a unique leader immediately before the new
tail; Corridor A then finishes directly because the new head is a follower. -/
theorem endpointSterile_phase_zero_no_leader_reaches_clean
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b : Fin n) (hndvd : ¬ k ∣ n)
    (hone : OneBarrierAt hk ring C b)
    (hsterile : EndpointSterile ring C b)
    (hphase : (C b).phase = false)
    (htailProbe : (C b).probe = false)
    (hzero : ∀ i : Fin n, (C i).leader = false) :
    ∃ w : List (Fin n), w.length ≤ 3 * n - 2 ∧
      Clean hk ring (runWord hk ring C w) := by
  have hn2 : 1 < n := by omega
  let h := ring.rightNeighbor b
  let tail := forwardEdgeWalk ring (ring.rightNeighbor h) (n - 2)
  let path := h :: tail
  let A := step hk ring C b
  let P := runWord hk ring A path
  let D := step hk ring P b
  have hpath : path = forwardEdgeWalk ring h (n - 1) := by
    have hnsub : n - 1 = (n - 2) + 1 := by omega
    simp [path, tail, hnsub, forwardEdgeWalk]
  have hheadRank : (cutCoord ring b h).val = 0 := by
    have hc := cutCoord_cutPos ring b (⟨0, ring.hn⟩ : Fin n)
    simpa [h] using congrArg Fin.val hc
  have hfit : (cutCoord ring b h).val + ((n - 2) + 1) < n := by omega
  have hgeom0 := forwardEdgeWalk_succ_geometry ring b h (n - 2) hfit
  have hnsub : n - 2 + 1 = n - 1 := by omega
  have hgeom :
      (∀ q ∈ path, (cutCoord ring b q).val < n - 1 ∧
        (cutCoord ring b (ring.rightNeighbor q)).val =
          (cutCoord ring b q).val + 1) ∧
      (cutCoord ring b
        (ring.rightNeighbor (path.getLast (by simp [path])))).val = n - 1 := by
    simpa [hpath, hheadRank, hnsub] using hgeom0
  have hord : ∀ q ∈ path, q ≠ b := by
    intro q hq hqb
    have hqrank := (hgeom.1 q hq).1
    subst q
    have hbRank : (cutCoord ring b b).val = n - 1 := by simp [tailCoord]
    omega
  have hanchorAvoid : ∀ q ∈ path, ring.rightNeighbor q ≠ h := by
    intro q hq hqh
    have hqr := (hgeom.1 q hq).2
    have hv := congrArg (fun i => (cutCoord ring b i).val) hqh
    omega
  have hend : ring.rightNeighbor (path.getLast (by simp [path])) = b := by
    rw [← cutPos_cutCoord ring b
      (ring.rightNeighbor (path.getLast (by simp [path])))]
    have hc : cutCoord ring b
        (ring.rightNeighbor (path.getLast (by simp [path]))) =
        tailCoord ring := by
      apply Fin.ext
      simpa [tailCoord] using hgeom.2
    rw [hc, cutPos_tailCoord]
  have hstart := barrier_phase_zero_starts_probe_circuit hk ring hn2 C b
    hndvd hone hsterile hphase htailProbe hzero
  have hchain : ForwardProbeChain ring path := by
    rw [hpath]
    exact forwardEdgeWalk_chain ring h (n - 1)
  have htrack := runWord_tracks_unique_probe_mark_frame hk ring hn2 A b h h
    tail hndvd hstart.1 (by simpa [path] using hord)
    (by simpa [path] using hchain) hstart.2.2.1
    hstart.2.2.2.1 hstart.2.2.2.2.1
    (by simpa [path] using hanchorAvoid) hstart.2.2.2.2.2
  have honeP : OneBarrierAt hk ring P b := by simpa [P, path] using htrack.1
  have hprobeP : (P b).probe = true := by
    have hp := htrack.2.1
    simpa [P, path, hend] using hp
  have hprobeUniqueP : ∀ i : Fin n, i ≠ b → (P i).probe = false := by
    intro i hib
    apply htrack.2.2.1 i
    simpa [path, hend] using hib
  have hbulletP : ∀ i : Fin n, i ≠ h → (P i).bullet = false := by
    simpa [P, path] using htrack.2.2.2.1
  have hzeroP : ∀ i : Fin n, (P i).leader = false := by
    simpa [P, path] using htrack.2.2.2.2.1
  have hphaseP : (P b).phase = true := by
    rw [htrack.2.2.2.2.2 b]
    exact hstart.2.1
  have hfinish := barrier_phase_one_unique_probe_creates_prepared_leader hk
    ring hn2 P b hndvd honeP hphaseP hprobeP hprobeUniqueP (by
      simpa [h] using hbulletP) hzeroP
  have hpreparedD : PreparedAt ring D h := by
    intro i _hi
    simpa [D, MarkFree] using hfinish.2.1 i
  have honeD : OneBarrierAt hk ring D h := by simpa [D] using hfinish.1
  have hleaderD : (D b).leader = true := by simpa [D] using hfinish.2.2.1
  have huniqueD : ∀ i : Fin n, (D i).leader = true → i = b := by
    simpa [D] using hfinish.2.2.2
  have hnonhead : b ≠ ring.rightNeighbor h := by
    simpa [h] using (rightNeighbor_sq_ne_self ring hn3 b).symm
  have hR : RightmostLeader ring D h b := by
    refine ⟨hleaderD, ?_⟩
    intro i hi
    rw [huniqueD i hi]
    exact Nat.le_refl _
  have hcorr := corridorA_reaches_result hk ring hn3 D h b hndvd honeD
    hpreparedD hR hnonhead
  have hcorrNoBirth := corridorA_no_leader_birth hk ring hn2 D h b hndvd
    honeD hnonhead
  have hcorrHead :
      ((runWord hk ring D (corridorAWord ring h b))
        (ring.rightNeighbor h)).leader = false := by
    cases hh : ((runWord hk ring D (corridorAWord ring h b))
        (ring.rightNeighbor h)).leader with
    | false => rfl
    | true =>
        have hold := hcorrNoBirth (ring.rightNeighbor h) hh
        have heq := huniqueD _ hold
        exact False.elim (hnonhead heq.symm)
  let wg := b :: (path ++ [b])
  let w := wg ++ corridorAWord ring h b
  refine ⟨w, ?_, ?_⟩
  · rw [List.length_append]
    have hwg : wg.length = n + 1 := by
      simp [wg, path, tail]
      omega
    have hwA := hcorr.1
    omega
  · have hrunG : runWord hk ring C wg = D := by
      simp [wg, D, P, A, runWord_append]
    change Clean hk ring
      (runWord hk ring C (wg ++ corridorAWord ring h b))
    rw [runWord_append, hrunG]
    exact corridorA_clean_of_head_follower hk ring
      (runWord hk ring D (corridorAWord ring h b)) h b hcorr.2 hcorrHead

/-- Complete zero-leader branch from the endpoint-sterile state delivered by
the parked sweep.  If the parked tail is already armed, one preliminary
advance sanitizes the new tail before entering the phase-zero probe circuit. -/
theorem endpointSterile_no_leader_reaches_clean {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b : Fin n) (hndvd : ¬ k ∣ n)
    (hone : OneBarrierAt hk ring C b)
    (hsterile : EndpointSterile ring C b)
    (htailProbe : (C b).probe = false)
    (hzero : ∀ i : Fin n, (C i).leader = false) :
    ∃ w : List (Fin n), w.length ≤ 4 * n - 2 ∧
      Clean hk ring (runWord hk ring C w) := by
  have hn2 : 1 < n := by omega
  cases hphase : (C b).phase with
  | false =>
      obtain ⟨w, hw, hclean⟩ :=
        endpointSterile_phase_zero_no_leader_reaches_clean hk ring hn3 C b
          hndvd hone hsterile hphase htailProbe hzero
      exact ⟨w, by omega, hclean⟩
  | true =>
      let h := ring.rightNeighbor b
      let D := step hk ring C b
      have hbar : IsBarrier hk (C b) (C h) :=
        (barrierAt_labelsOf_iff hk ring C b).mp ((hone b).2 rfl)
      have htrans : CenteredRenewal.transition hk (C b) (C h) =
          (probeHitsBarrier (C b),
            { C h with
              label := succLabel hk (C b).label
              phase := false
              bullet := false
              probe := false }) := by
        rw [CenteredRenewal.transition_of_barrier hk _ _ hbar]
        exact CenteredRenewal.barrierStep_phase_one hk _ _ hphase
      have hre : h ≠ b := rightNeighbor_ne_self ring hn2 b
      have honeD : OneBarrierAt hk ring D h := by
        exact barrier_phase_one_advances_unique_barrier hk ring hn2 C b hndvd
          hone hphase
      have hfresh := advance_sanitizes_new_tail hk ring hn2 C b hone hphase
      have hphaseD : (D h).phase = false := hfresh.1
      have htailProbeD : (D h).probe = false := hfresh.2.2
      have hleaders := barrier_phase_one_leaders_eq hk ring hn2 C b hone
        hphase htailProbe
      have hzeroD : ∀ i : Fin n, (D i).leader = false := by
        intro i
        rw [hleaders i]
        exact hzero i
      dsimp [h] at htrans hre
      have hsterileD : EndpointSterile ring D h := by
        constructor
        · intro i hih
          by_cases hib : i = b
          · subst i
            simp [D, step, PopulationProtocol.step,
              CenteredRenewal.protocol, htrans, probeHitsBarrier, htailProbe]
          · have hp := hsterile.1 i hib
            have hih' : i ≠ ring.rightNeighbor b := by simpa [h] using hih
            simp [D, step, PopulationProtocol.step, CenteredRenewal.protocol,
              htrans, hib, hih', hp]
        · intro i _hiNewHead
          by_cases hib : i = b
          · subst i
            have hb := hsterile.2 b (Ne.symm hre)
            simpa [D, step, PopulationProtocol.step,
              CenteredRenewal.protocol, htrans, probeHitsBarrier,
              htailProbe] using hb
          · by_cases hih : i = h
            · subst i
              simp [D, step, PopulationProtocol.step,
                CenteredRenewal.protocol, htrans, h, hre]
            · have hih' : i ≠ ring.rightNeighbor b := by simpa [h] using hih
              have hb := hsterile.2 i hih'
              simp [D, step, PopulationProtocol.step,
                CenteredRenewal.protocol, hib, hih', hb]
      obtain ⟨w, hw, hclean⟩ :=
        endpointSterile_phase_zero_no_leader_reaches_clean hk ring hn3 D h
          hndvd honeD hsterileD hphaseD htailProbeD hzeroD
      refine ⟨b :: w, ?_, ?_⟩
      · simp
        omega
      · simpa [D] using hclean

/-- Global deterministic cleanup capstone.  From every centered one-barrier
configuration on a ring of size at least three, an explicit finite interaction
word of length at most `8n-5` reaches the repository's exact `Clean`
predicate. -/
theorem oneBarrier_exists_cleanupWord {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b : Fin n) (hndvd : ¬ k ∣ n)
    (hone : OneBarrierAt hk ring C b) :
    ∃ w : List (Fin n), w.length ≤ 8 * n - 5 ∧
      Clean hk ring (runWord hk ring C w) := by
  have hn2 : 1 < n := by omega
  let ws := parkedSweepWord ring b
  let S := runWord hk ring C ws
  have hsweep := parkedSweepWord_endpointSterile hk ring hn2 C b hndvd hone
  have honeS : OneBarrierAt hk ring S b := by simpa [S, ws] using hsweep.1
  have hsterileS : EndpointSterile ring S b := by
    simpa [S, ws] using hsweep.2
  let wd := endpointDischargeWord S b
  let b' := endpointDischargeBarrier ring S b
  let D := runWord hk ring S wd
  have hdis := endpointSterile_discharge hk ring hn2 S b hndvd honeS hsterileS
  have hwd : wd.length ≤ 1 := by simpa [wd] using hdis.1
  have honeD : OneBarrierAt hk ring D b' := by
    simpa [D, b', wd] using hdis.2.1
  have hpreparedD : PreparedAt ring D b' := by
    simpa [D, b', wd] using hdis.2.2.1
  by_cases hHas : ∃ i : Fin n, (D i).leader = true
  · obtain ⟨wt, hwt, hclean⟩ := prepared_with_leader_reaches_clean hk ring
      hn3 D b' hndvd honeD hpreparedD hHas
    refine ⟨ws ++ wd ++ wt, ?_, ?_⟩
    · simp only [List.length_append]
      have hws : ws.length = 4 * (n - 1) := by
        simpa [ws] using parkedSweepWord_length ring b
      omega
    · rw [runWord_append, runWord_append]
      simpa [S, D] using hclean
  · have hzeroD : ∀ i : Fin n, (D i).leader = false := by
      intro i
      cases hi : (D i).leader with
      | false => rfl
      | true => exact False.elim (hHas ⟨i, hi⟩)
    have htailProbeS : (S b).probe = false := by
      cases hp : (S b).probe with
      | false => rfl
      | true =>
          have hleaderD : (D b).leader = true := by
            exact hdis.2.2.2 hp
          exact False.elim
            (Bool.noConfusion ((hzeroD b).symm.trans hleaderD))
    have hwdNil : wd = [] := by
      simp [wd, endpointDischargeWord, htailProbeS]
    have hb'Eq : b' = b := by
      simp [b', endpointDischargeBarrier, htailProbeS]
    have hDEq : D = S := by simp [D, hwdNil]
    have hzeroS : ∀ i : Fin n, (S i).leader = false := by
      intro i
      rw [← hDEq]
      exact hzeroD i
    obtain ⟨wt, hwt, hclean⟩ := endpointSterile_no_leader_reaches_clean hk
      ring hn3 S b hndvd honeS hsterileS htailProbeS hzeroS
    refine ⟨ws ++ wt, ?_, ?_⟩
    · rw [List.length_append]
      have hws : ws.length = 4 * (n - 1) := by
        simpa [ws] using parkedSweepWord_length ring b
      omega
    · rw [runWord_append]
      simpa [S] using hclean

theorem terminal_budget_arithmetic (n : Nat) (hn3 : 3 ≤ n) :
    (2 * n - 3) + 4 + (2 * n - 3) ≤ 4 * n - 2 := by omega

theorem global_budget_arithmetic (n : Nat) (hn3 : 3 ≤ n) :
    4 * (n - 1) + (4 * n - 1) = 8 * n - 5 := by omega

end OneBarrierCleanup
end CenteredRenewal
end AAFJPK
