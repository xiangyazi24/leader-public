import Leader.Wu.Birth.CheckPermitRepairLeaf
import Leader.Wu.Safety.NoCheckBirthOutputLegitimacy
import Leader.Wu.Elimination.BirthDispatcherCollision
import Leader.Wu.Elimination.SinkTwoGapEpochSuccessor

/-!
R1LegitKernel: the all-futures reference kernel for the actual R1 row.
The full-state transition is never replaced by an observed transition.
Output-vector preservation is derived from uniqueness and no-new-leader.
-/

namespace R1LegitKernel

open PPLLResearchFormulation PPLLExpiringComparisonRepair

set_option autoImplicit false

variable {n psi kappa tau : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  Fin n → ExpiringAgentState psi kappa tau

abbrev protocolR1 (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (kappa tau : Nat) : PopulationProtocol :=
  BirthCheckPermitRepair.protocol hpsi (by decide : 0 < 2)
    h2 kappa tau

/-- The carrier's actual Bool output. -/
def outputR1 (u : ExpiringAgentState psi kappa tau) : Bool :=
  u.core.core.leader

/-- The semantic interface asks for Bool → Bool, not Bool → Prop. -/
def isLeaderR1 (b : Bool) : Bool := b

theorem protocolR1_output (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (u : ExpiringAgentState psi kappa tau) :
    (protocolR1 hpsi h2 kappa tau).output u = outputR1 u := rfl

/-- The existing protocol schedule on exactly the R1 physical step. -/
abbrev runR1 (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (w : List (Fin n)) : FC n psi kappa tau :=
  runSchedule (protocolR1 hpsi h2 kappa tau) ring C w

/-- Actual post-expiry, post-normalization, pre-finalPhysical endpoints. -/
def metadataR1 (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau :=
  let q := BirthCheckPermitRepair.expiring
    hpsi (by decide : 0 < 2) h2 l r
  (K2BirthLeaderNormalize.normalizeLeader hpsi q.1,
    K2BirthLeaderNormalize.normalizeLeader hpsi q.2)

/-- A birth compares the ORIGINAL endpoints to the actual R1 metadata,
not to the final leader count and not to an old-consumer successor. -/
def birthEventR1 (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau) : Bool :=
  let q := metadataR1 hpsi h2 l r
  K2BirthDispatcher.newborn l q.1 ||
    K2BirthDispatcher.newborn r q.2

/-- Definitional identification of the exact metadata cut in the row. -/
theorem row_eq_finalPhysical (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau) :
    BirthCheckPermitRepair.row hpsi (by decide : 0 < 2) h2 l r =
      K2BirthDispatcher.finalPhysical hpsi l r
        (metadataR1 hpsi h2 l r).1 (metadataR1 hpsi h2 l r).2 := rfl

def NoBirthNowR1 (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) : Prop :=
  ∀ e : Fin n,
    birthEventR1 hpsi h2 (C e) (C (ring.rightNeighbor e)) = false

/-- The current-state envelope for the R1 row. -/
def SafeNowR1 (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) : Prop :=
  PPLLNoCheckBirthOutputLegitimacy.OutputLegit hpsi ring C ∧
    NoBirthNowR1 hpsi h2 ring C

/-- All finite words, including the empty word. This stores no output
preservation premise; that consequence is proved below. -/
def LegitR1 (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) : Prop :=
  ∀ w : List (Fin n),
    SafeNowR1 hpsi h2 ring (runR1 hpsi h2 ring C w)

theorem legitR1_now (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (hC : LegitR1 hpsi h2 ring C) : SafeNowR1 hpsi h2 ring C :=
  hC []

/-- A continuation from the successor is the word e :: w from C. -/
theorem legitR1_step (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (hC : LegitR1 hpsi h2 ring C) (e : Fin n) :
    LegitR1 hpsi h2 ring
      (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring C e) := by
  intro w
  exact hC (e :: w)

theorem legitR1_closed (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred (protocolR1 hpsi h2 kappa tau)
      ring (LegitR1 hpsi h2 ring) := by
  intro C hC D hstep
  obtain ⟨e, rfl⟩ := hstep
  exact legitR1_step hpsi h2 ring C hC e

/-- Current uniqueness is the empty-word projection, with Bool output. -/
theorem legitR1_unique (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (hC : LegitR1 hpsi h2 ring C) :
    UniqueLeaderOutput (protocolR1 hpsi h2 kappa tau) n C
      isLeaderR1 := by
  have hs := (legitR1_now hpsi h2 ring C hC).1
  obtain ⟨l, hl, honly⟩ := hs.unique_leader
  refine ⟨l, ?_, ?_⟩
  · change (C l).core.core.leader = true
    exact hl
  · intro i hi
    apply honly i
    change (C i).core.core.leader = true at hi
    exact hi

theorem legitR1_run (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (hC : LegitR1 hpsi h2 ring C) (w : List (Fin n)) :
    LegitR1 hpsi h2 ring (runR1 hpsi h2 ring C w) := by
  exact (legitR1_closed (kappa := kappa) (tau := tau)
    hpsi h2 ring).reachable hC
      (runSchedule_reachable (protocolR1 hpsi h2 kappa tau) ring C w)

-- END PART 1
/-- The actual collision/K2 tail preserves a false leader bit separately
at each endpoint; no global safety or leaderlessness premise is used. -/
private theorem collisionRow_preserves_followers (hpsi : 0 < psi)
    (l r : ExpiringAgentState psi kappa tau) :
    (l.core.core.leader = false →
      (K2BirthDispatcher.collisionRow hpsi l r).1.core.core.leader = false) ∧
    (r.core.core.leader = false →
      (K2BirthDispatcher.collisionRow hpsi l r).2.core.core.leader = false) := by
  by_cases hb : l.core.core.leader = true ∧ r.core.core.leader = true
  · constructor
    · intro hl
      have hbad : false = true := hl.symm.trans hb.1
      cases hbad
    · intro hr
      have hbad : false = true := hr.symm.trans hb.2
      cases hbad
  · have heq := K2BirthDispatcher.collisionRow_of_not_both hpsi l r hb
    have hk := LDSinkTwoGapEpochSuccessor.kernelC_no_leader_creation
      (by decide : 0 < 1)
      (ExpiringK2Projection.observeCell l) (ExpiringK2Projection.observeCell r)
    constructor
    · intro hl
      rw [heq]
      change (LDSinkKernelC.sinkKernelC (by decide : 0 < 1)
        (ExpiringK2Projection.observeCell l)
        (ExpiringK2Projection.observeCell r)).1.leader = false
      exact hk.1 hl
    · intro hr
      rw [heq]
      change (LDSinkKernelC.sinkKernelC (by decide : 0 < 1)
        (ExpiringK2Projection.observeCell l)
        (ExpiringK2Projection.observeCell r)).2.leader = false
      exact hk.2 hr

private theorem newborn_false_follower
    (old out : ExpiringAgentState psi kappa tau)
    (hNB : K2BirthDispatcher.newborn old out = false)
    (hOld : old.core.core.leader = false) :
    out.core.core.leader = false := by
  simpa [K2BirthDispatcher.newborn, hOld] using hNB

/-- Full R1 row: no metadata birth implies endpointwise non-creation.
The event is taken before the same-row collision/elimination tail. -/
theorem row_followers_of_no_birth (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hNB : birthEventR1 hpsi h2 l r = false) :
    (l.core.core.leader = false →
      (BirthCheckPermitRepair.row hpsi (by decide : 0 < 2)
        h2 l r).1.core.core.leader = false) ∧
    (r.core.core.leader = false →
      (BirthCheckPermitRepair.row hpsi (by decide : 0 < 2)
        h2 l r).2.core.core.leader = false) := by
  let m := metadataR1 hpsi h2 l r
  have hb : K2BirthDispatcher.newborn l m.1 = false ∧
      K2BirthDispatcher.newborn r m.2 = false := by
    simpa only [birthEventR1, m, Bool.or_eq_false_iff] using hNB
  have heq : BirthCheckPermitRepair.row
      hpsi (by decide : 0 < 2) h2 l r =
      K2BirthDispatcher.collisionRow hpsi m.1 m.2 := by
    exact (row_eq_finalPhysical hpsi h2 l r).trans
      (K2BirthDispatcher.finalPhysical_of_no_birth
        hpsi l r m.1 m.2 hb.1 hb.2)
  have hc := collisionRow_preserves_followers hpsi m.1 m.2
  constructor
  · intro hl
    rw [heq]
    exact hc.1 (newborn_false_follower l m.1 hb.1 hl)
  · intro hr
    rw [heq]
    exact hc.2 (newborn_false_follower r m.2 hb.2 hr)

/-- The exact ring update, including left-output priority on an alias. -/
theorem step1_follower_of_no_birth (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) (e : Fin n)
    (hNB : birthEventR1 hpsi h2 (C e) (C (ring.rightNeighbor e)) = false)
    (i : Fin n) (hFollower : (C i).core.core.leader = false) :
    (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring C e i).core.core.leader =
      false := by
  have hq := row_followers_of_no_birth
    hpsi h2 (C e) (C (ring.rightNeighbor e)) hNB
  simp only [BirthCheckPermitRepairLeaf.step1,
    PopulationProtocol.step, BirthCheckPermitRepair.protocol]
  split
  · rename_i hi
    subst i
    exact hq.1 hFollower
  · split
    · rename_i hi
      subst i
      exact hq.2 hFollower
    · exact hFollower

/-- Every leader in the new configuration was a leader at the same site
before the step. No whole-configuration leaderlessness premise is required. -/
theorem step1_no_new_leader_of_no_birth
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (e : Fin n)
    (hNB : birthEventR1 hpsi h2 (C e) (C (ring.rightNeighbor e)) = false)
    (i : Fin n)
    (hNew : (BirthCheckPermitRepairLeaf.step1
      hpsi h2 ring C e i).core.core.leader = true) :
    (C i).core.core.leader = true := by
  cases hOld : (C i).core.core.leader with
  | false =>
      have hz := step1_follower_of_no_birth hpsi h2 ring C e hNB i hOld
      have hbad : false = true := hz.symm.trans hNew
      cases hbad
  | true => rfl

/-- Uniqueness alone does not fix a vector. This lemma additionally uses
pointwise no-new-leader and existence of the successor's unique leader. -/
private theorem bool_vectors_eq_of_unique_no_new (A B : Fin n → Bool)
    (hA : ∃ a : Fin n, A a = true ∧ ∀ i : Fin n, A i = true → i = a)
    (hB : ∃ b : Fin n, B b = true ∧ ∀ i : Fin n, B i = true → i = b)
    (hBack : ∀ i : Fin n, B i = true → A i = true)
    (i : Fin n) : B i = A i := by
  obtain ⟨a, ha, honly⟩ := hA
  obtain ⟨b, hb, _⟩ := hB
  have hba : b = a := honly b (hBack b hb)
  subst b
  cases hAi : A i with
  | false =>
      cases hBi : B i with
      | false => rfl
      | true =>
          have hbad : false = true := hAi.symm.trans (hBack i hBi)
          cases hbad
  | true =>
      have hi : i = a := honly i hAi
      subst i
      exact hb

-- END PART 2
/-- The output proof uses empty-word uniqueness, successor uniqueness
from closure, and the physical no-new-leader lemma. -/
theorem step1_output_eq_of_legitR1
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (hC : LegitR1 hpsi h2 ring C)
    (e i : Fin n) :
    (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring C e i).core.core.leader =
      (C i).core.core.leader := by
  have hNB := (legitR1_now hpsi h2 ring C hC).2 e
  exact bool_vectors_eq_of_unique_no_new
    (fun j => (C j).core.core.leader)
    (fun j => (BirthCheckPermitRepairLeaf.step1
      hpsi h2 ring C e j).core.core.leader)
    (legitR1_unique hpsi h2 ring C hC)
    (legitR1_unique hpsi h2 ring _ (legitR1_step hpsi h2 ring C hC e))
    (fun j hj => step1_no_new_leader_of_no_birth
      hpsi h2 ring C e hNB j hj) i

theorem legitR1_output_preserving (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) :
    StepOutputPreservingOn (protocolR1 hpsi h2 kappa tau)
      ring (LegitR1 hpsi h2 ring) := by
  intro C hC D hstep i
  obtain ⟨e, rfl⟩ := hstep
  change
    (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring C e i).core.core.leader =
      (C i).core.core.leader
  exact step1_output_eq_of_legitR1 hpsi h2 ring C hC e i

theorem legitR1_run_output (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (hC : LegitR1 hpsi h2 ring C) (w : List (Fin n)) (i : Fin n) :
    (runR1 hpsi h2 ring C w i).core.core.leader =
      (C i).core.core.leader := by
  induction w generalizing C with
  | nil => rfl
  | cons e w ih =>
      change
        (runR1 hpsi h2 ring
          (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring C e) w i).core.core.leader =
          (C i).core.core.leader
      exact (ih (C := BirthCheckPermitRepairLeaf.step1 hpsi h2 ring C e)
        (legitR1_step hpsi h2 ring C hC e)).trans
          (step1_output_eq_of_legitR1 hpsi h2 ring C hC e i)

/-- Equivalent explicit presentation: unique now, unique after every
word, and the same whole Bool output vector after every word. The
original SafeNow clauses are retained, not silently weakened. -/
theorem legitR1_iff_all_words (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) :
    LegitR1 hpsi h2 ring C ↔
      UniqueLeaderOutput (protocolR1 hpsi h2 kappa tau) n C isLeaderR1 ∧
      ∀ w : List (Fin n),
        SafeNowR1 hpsi h2 ring (runR1 hpsi h2 ring C w) ∧
        UniqueLeaderOutput (protocolR1 hpsi h2 kappa tau) n
          (runR1 hpsi h2 ring C w) isLeaderR1 ∧
        (fun i : Fin n => outputR1 (runR1 hpsi h2 ring C w i)) =
          (fun i : Fin n => outputR1 (C i)) := by
  constructor
  · intro hC
    refine ⟨legitR1_unique hpsi h2 ring C hC, ?_⟩
    intro w
    refine ⟨hC w, ?_, ?_⟩
    · exact legitR1_unique hpsi h2 ring _ (legitR1_run hpsi h2 ring C hC w)
    · funext i
      exact legitR1_run_output hpsi h2 ring C hC w i
  · intro h
    intro w
    exact (h.2 w).1

/-- Semantic safety for precisely the R1 protocol and its Bool output. -/
theorem legitR1_isSafe (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (hC : LegitR1 hpsi h2 ring C) :
    PopulationProtocol.IsSafe (protocolR1 hpsi h2 kappa tau)
      ring C isLeaderR1 := by
  exact PPLLResearchFormulation.isSafe_of_operational_legitimacy
    (protocolR1 hpsi h2 kappa tau) ring isLeaderR1
    (LegitR1 hpsi h2 ring)
    (legitR1_closed (kappa := kappa) (tau := tau) hpsi h2 ring)
    (legitR1_unique hpsi h2 ring)
    (legitR1_output_preserving (kappa := kappa) (tau := tau) hpsi h2 ring)
    hC

/-- An independently certified two-leader word excludes its starting
configuration from the kernel. No nine-cell fixture is assumed here. -/
theorem not_legitR1_of_two_leaders
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (w : List (Fin n))
    (i j : Fin n) (hne : i ≠ j)
    (hi : (runR1 hpsi h2 ring C w i).core.core.leader = true)
    (hj : (runR1 hpsi h2 ring C w j).core.core.leader = true) :
    ¬ LegitR1 hpsi h2 ring C := by
  intro hC
  obtain ⟨a, _, honly⟩ := legitR1_unique hpsi h2 ring
    (runR1 hpsi h2 ring C w) (legitR1_run hpsi h2 ring C hC w)
  exact hne ((honly i hi).trans (honly j hj).symm)

/- PLAN
Regression being certified elsewhere: the C9 case has n=9, psi=3,
kappa=3, tau=48, width=2; labels i mod 3; a clean sole leader at 0;
clean passive background; and at sites 3,4,5 respectively:
  BirthCheckPermitRepair.tok 0 true true
  BirthCheckPermitRepair.tok 1 false false
  BirthCheckPermitRepair.tok 2 true false
The word [3,4] leaves leaders at both 0 and 5. Once the concrete C9
and that full-ring word certificate are imported, instantiate
not_legitR1_of_two_leaders to prove that C9 is not in LegitR1.
There is deliberately no axiom, unchecked fixture, or regression
proof placeholder outside this comment.

Separate work: nonemptiness of this kernel; an inhabited structural
subkernel with source/writer/expiry closure; physical entrance or a
load-safe contract; original-scheduler no-birth/elimination mass; and
safety of the actual final B9+R1 composition. None follows merely from
the all-futures definition or from the conditional safety theorem here.
-/

end R1LegitKernel

#print axioms R1LegitKernel.legitR1_closed
#print axioms R1LegitKernel.legitR1_unique
#print axioms R1LegitKernel.step1_no_new_leader_of_no_birth
#print axioms R1LegitKernel.legitR1_output_preserving
#print axioms R1LegitKernel.legitR1_isSafe

-- END PART 3
