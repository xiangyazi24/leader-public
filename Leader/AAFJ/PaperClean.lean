import Leader.AAFJ.MultiBarrier.ReachesOneBarrier

/-!
# Paper-facing interfaces for AAFJ Section 9

This module is a source adapter for the qualitative part of the AAFJ journal
argument.  The transition, charged-barrier algebra, and one-barrier closure
live in the lower-level modules.  Here we expose the paper's odd-ring/P₂ and
fixed-`k`/Pₖ interfaces with the source convention that marks are forbidden
on the clockwise cut interval from the unique leader through the barrier tail.

For general fixed `k`, the multi-barrier route is expressed by additive defect
charge and strict `barrierCount` descent; it does not import the P₂-only
phrase that a collision makes both barriers disappear.  The finite descent to
one physical barrier is provided by `Leader.AAFJ.MultiBarrier.ReachesOneBarrier`.  The
subsequent one-barrier sanitation interface is `k`-uniform and retains the
repository condition `3 ≤ n`.

The adapter states only the multi-barrier half of Lemma 9.2: the
arbitrary-configuration finite path to one physical barrier is proved, while
the one-barrier path to `Clean` remains open.  Consequently the P₂/Pₖ wrappers
below are closure, barrier-descent, and one-barrier facts, not a complete
self-stabilization theorem.

Source anchors: AAFJ journal §9, Clean and Lemma 9.1 on printed pp.24--25;
Protocol 6 on p.25; Lemma 9.2 and Theorems 9.3--9.4 on p.26.
-/

namespace AAFJPaper9

open AAFJPK
open AAFJPK.BarrierAlgebra
open AAFJPK.SingleBarrierSanitation

set_option autoImplicit false

/-! ## Paper parameter predicates -/

/-- The odd rings to which the paper's P₂ branch applies in this repository.

The lower bound excludes the singleton self-edge semantics of `DirectedRing`;
the exact-size family handles `n = 1` separately. -/
def OddRing (n : Nat) : Prop :=
  3 ≤ n ∧ ∃ m : Nat, n = 2 * m + 1

theorem OddRing.not_two_dvd {n : Nat} (hodd : OddRing n) : ¬ 2 ∣ n := by
  intro hdiv
  obtain ⟨q, hq⟩ := hdiv
  obtain ⟨m, hm⟩ := hodd.2
  omega

theorem OddRing.three_le {n : Nat} (hodd : OddRing n) : 3 ≤ n :=
  hodd.1

/-! ## The paper's interval form of `Clean` -/

/-- A mark-free suffix in the canonical cut coordinates.

`i.val ≥ ell.val` is the paper's clockwise interval from the leader through
the barrier tail.  The lower-level development uses the equivalent implication
`Marked i → i.val < ell.val`; keeping both forms makes the source correspondence
explicit. -/
def PaperCleanData {n k : Nat} (X : Fin n → State k) (ell : Fin n) : Prop :=
  (X ell).leader = true ∧
    (∀ i : Fin n, (X i).leader = true → i = ell) ∧
    ∀ i : Fin n, ell.val ≤ i.val → ¬ Marked (X i)

instance instDecidablePaperCleanData {n k : Nat}
    (X : Fin n → State k) (ell : Fin n) :
    Decidable (PaperCleanData X ell) := by
  unfold PaperCleanData
  infer_instance

theorem paperCleanData_iff_cleanData {n k : Nat}
    (X : Fin n → State k) (ell : Fin n) :
    PaperCleanData X ell ↔ CleanData X ell := by
  constructor
  · rintro ⟨hleader, hunique, hforbid⟩
    refine ⟨hleader, hunique, ?_⟩
    intro i hmark
    by_cases hlt : i.val < ell.val
    · exact hlt
    · exact (hforbid i (by omega) hmark).elim
  · rintro ⟨hleader, hunique, hmarks⟩
    refine ⟨hleader, hunique, ?_⟩
    intro i hge hmark
    exact (by omega : ¬ i.val < ell.val) (hmarks i hmark)

/-! ## Physical paper predicates -/

/-- A source-facing clean witness with an explicit barrier and leader. -/
def PaperCleanAt {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (barrier leader : Fin n) : Prop :=
  OneBarrierAt hk ring C barrier ∧
    PaperCleanData (cutView ring barrier C) (cutCoord ring barrier leader)

/-- Clean configurations with a fixed physical leader, in paper notation. -/
def PaperCleanForLeader {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (leader : Fin n) (C : Fin n → State k) : Prop :=
  ∃ barrier : Fin n, PaperCleanAt hk ring C barrier leader

/-- The existential paper `Clean` predicate. -/
def PaperClean {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) : Prop :=
  ∃ leader : Fin n, PaperCleanForLeader hk ring leader C

theorem paperCleanAt_iff_cleanAt {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k)
    (barrier leader : Fin n) :
    PaperCleanAt hk ring C barrier leader ↔
      CleanAt hk ring C barrier leader := by
  constructor
  · rintro ⟨hone, hdata⟩
    exact ⟨hone, (paperCleanData_iff_cleanData _ _).mp hdata⟩
  · rintro ⟨hone, hdata⟩
    exact ⟨hone, (paperCleanData_iff_cleanData _ _).mpr hdata⟩

theorem paperCleanForLeader_iff_cleanForLeader {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (leader : Fin n)
    (C : Fin n → State k) :
    PaperCleanForLeader hk ring leader C ↔
      CleanForLeader hk ring leader C := by
  constructor
  · rintro ⟨barrier, hclean⟩
    exact ⟨barrier, (paperCleanAt_iff_cleanAt hk ring C barrier leader).mp hclean⟩
  · rintro ⟨barrier, hclean⟩
    exact ⟨barrier, (paperCleanAt_iff_cleanAt hk ring C barrier leader).mpr hclean⟩

theorem paperClean_iff_clean {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) :
    PaperClean hk ring C ↔ Clean hk ring C := by
  constructor
  · rintro ⟨leader, hclean⟩
    exact ⟨leader,
      (paperCleanForLeader_iff_cleanForLeader hk ring leader C).mp hclean⟩
  · rintro ⟨leader, hclean⟩
    exact ⟨leader,
      (paperCleanForLeader_iff_cleanForLeader hk ring leader C).mpr hclean⟩

/-! ## Paper-facing safety wrappers -/

theorem paperCleanAt_isSafe {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) (barrier leader : Fin n)
    (hclean : PaperCleanAt hk ring C barrier leader) :
    PopulationProtocol.IsSafe (AAFJPK.protocol k hk) ring C (fun bit => bit) := by
  exact cleanAt_isSafe hk ring hn3 hndvd C barrier leader
    ((paperCleanAt_iff_cleanAt hk ring C barrier leader).mp hclean)

theorem paperCleanForLeader_isSafe {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) (leader : Fin n)
    (hclean : PaperCleanForLeader hk ring leader C) :
    PopulationProtocol.IsSafe (AAFJPK.protocol k hk) ring C (fun bit => bit) := by
  exact cleanForLeader_isSafe hk ring hn3 hndvd C leader
    ((paperCleanForLeader_iff_cleanForLeader hk ring leader C).mp hclean)

/-! ## Lemma 9.1: closure and same physical leader -/

/-- Paper Lemma 9.1 for P₂ on odd rings.

The barrier witness may move, but the physical leader `leader` is unchanged.
The proof is the already-verified generalized clean-closure theorem, exposed
through the paper's interval predicate.  This is the fixed-`k` specialization
`k = 2` of the literal `AAFJPK.protocol`; the exact-family selector is not
part of the journal interface. -/
theorem paperLemma9_1_sameLeader {n : Nat} (hodd : OddRing n)
    (ring : DirectedRing n) (leader : Fin n)
    {C C' : Fin n → State 2}
    (hC : PaperCleanForLeader (by decide) ring leader C)
    (hr : PopulationProtocol.Reachable
      (AAFJPK.protocol 2 (by decide)) ring C C') :
    PaperCleanForLeader (by decide) ring leader C' := by
  have hclean : CleanForLeader (by decide) ring leader C :=
    (paperCleanForLeader_iff_cleanForLeader (by decide) ring leader C).mp hC
  have hclean' := cleanForLeader_reachable (by decide) ring hodd.three_le
    hodd.not_two_dvd leader hclean hr
  exact (paperCleanForLeader_iff_cleanForLeader
    (by decide) ring leader C').mpr hclean'

/-- The same Lemma 9.1 bridge with the moving barrier made explicit. -/
theorem paperLemma9_1_sameLeader_at {n : Nat} (hodd : OddRing n)
    (ring : DirectedRing n) (leader : Fin n)
    {C C' : Fin n → State 2} (barrier : Fin n)
    (hC : PaperCleanAt (by decide) ring C barrier leader)
    (hr : PopulationProtocol.Reachable
      (AAFJPK.protocol 2 (by decide)) ring C C') :
    ∃ barrier' : Fin n, PaperCleanAt (by decide) ring C' barrier' leader := by
  have hfor : PaperCleanForLeader (by decide) ring leader C :=
    ⟨barrier, hC⟩
  obtain ⟨barrier', hC'⟩ := paperLemma9_1_sameLeader hodd ring leader hfor hr
  exact ⟨barrier', hC'⟩

/-! ## Theorem 9.4: fixed-`k` barrier and one-barrier interfaces -/

/-- The proved multi-barrier half of paper Lemma 9.2 for odd-ring P₂.

Every starting configuration reaches a state with exactly one physical
barrier.  This does not include the remainder of Lemma 9.2, which sanitizes a
one-barrier state to `Clean`. -/
theorem paperLemma9_2_reaches_oneBarrierAt {n : Nat} (hodd : OddRing n)
    (ring : DirectedRing n) (C : Fin n → State 2) :
    ∃ D : Fin n → State 2, ∃ barrier : Fin n,
      PopulationProtocol.Reachable
          (AAFJPK.protocol 2 (by decide)) ring C D ∧
      OneBarrierAt (by decide) ring D barrier := by
  have hn3 : 2 < n := by
    have := hodd.three_le
    omega
  exact AAFJPK.OriginalQualitative.reaches_oneBarrierAt
    (by decide) ring hn3 hodd.not_two_dvd C

/-- The fixed-`k` arithmetic entry point used by the Pₖ proof.

For `k ≥ 2` and `k ∤ n`, every full configuration has a source-level barrier.
This is the part of Theorem 9.4 that is independent of Lemma 9.2's finite
cleaning path.  The fixed-`k` descent is through the defect-sum law and
`barrierCount`; no P₂-specific two-barrier collision claim is used. -/
theorem paperTheorem9_4_barrier_exists {n k : Nat}
    (hk2 : 2 ≤ k) (ring : DirectedRing n) (C : Fin n → State k)
    (hndvd : ¬ k ∣ n) :
    ∃ e : Fin n,
      IsBarrier (by omega : 0 < k) (C e)
        (C (ring.rightNeighbor e)) := by
  exact exists_state_barrier_of_not_dvd (by omega) ring C hndvd

/-- The fixed-`k` multi-barrier descent used by the generalized paper claim.

For `k ≥ 2`, `3 ≤ n`, and `k ∤ n`, every starting configuration reaches
an exactly-one-barrier state.  The proof iterates only strict decreases of
`barrierCount`; it makes no generic claim that one collision removes exactly
two barriers.  The one-barrier-to-`Clean` part of Theorem 9.4 remains open. -/
theorem paperTheorem9_4_reaches_oneBarrierAt {n k : Nat}
    (hk2 : 2 ≤ k) (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (hndvd : ¬ k ∣ n) :
    ∃ D : Fin n → State k, ∃ barrier : Fin n,
      PopulationProtocol.Reachable
          (AAFJPK.protocol k (by omega)) ring C D ∧
      OneBarrierAt (by omega) ring D barrier := by
  exact AAFJPK.OriginalQualitative.reaches_oneBarrierAt
    (by omega) ring (by omega) hndvd C

/-- A non-singleton Pₖ step preserves the one-barrier slice.

This is the invariant half of the generalized theorem; it still needs the
paper's Lemma 9.2 reachability construction to become a self-stabilization
theorem.  The separate `OriginalQualitative.reaches_oneBarrierAt` theorem
closes only the strict multi-barrier descent to this slice; the
one-barrier-to-`Clean` construction remains a distinct obligation. -/
theorem paperTheorem9_4_oneBarrier_preserved {n k : Nat}
    (hk2 : 2 ≤ k) (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (e : Fin n) (hndvd : ¬ k ∣ n)
    (hone : barrierCount (by omega) ring (labelsOf C) = 1) :
    barrierCount (by omega) ring
        (labelsOf ((AAFJPK.protocol k (by omega)).step ring C e)) = 1 := by
  exact protocol_step_preserves_oneBarrier (by omega) ring (by omega)
    C e hndvd hone

end AAFJPaper9

#print axioms AAFJPaper9.paperLemma9_1_sameLeader
#print axioms AAFJPaper9.paperLemma9_2_reaches_oneBarrierAt
#print axioms AAFJPaper9.paperTheorem9_4_barrier_exists
#print axioms AAFJPaper9.paperTheorem9_4_reaches_oneBarrierAt
