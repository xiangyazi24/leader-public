import Leader.L3.Headline.Assembly
import Leader.L3.SealedPrep
import Leader.L3.NativeLift

/-!
Reference preparation: checked interface audit and a
conditional physical first-exit stage.

The paper's singleton preparation is NOT the two-leader sealed-sector
preparation. In particular, the stage proved at the bottom of this
file has a different start and a different stopping target from the
paper's sigma_1 -> sigma_p stage. The extra stopping alternative
means a physical grant has reappeared; it is not a prepared state.
No claim about extinction of inherited authority is made here, since
that is a property of the decorated reference history rather than of
the bare Cartesian configuration.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The physical part of the paper's sigma_1 predicate. Extinction
of inherited generator authority has to live in the reference
decoration and is deliberately not hidden in this definition. -/
def ReferencePreparationSingletonCore {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n) : Prop :=
  Protected ring (nativeProjection C) ∧
  NativeLiftGrantFree C ∧
  OneNativeLeader (nativeProjection C)

/-- The native/candidate part of the paper's sigma_p target.
The paper obtains the stronger bullet-free, all-signals-one
endpoint. The decorated inherited-authority condition is separate. -/
def ReferencePreparationPreparedCore {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n) : Prop :=
  Protected ring (nativeProjection C) ∧
  NativeLiftGrantFree C ∧
  OneNativeLeader (nativeProjection C) ∧
  C_native ring (nativeProjection C) ∧
  (∀ i : Fin n,
    (nativeProjection C i).b = (0 : Fin 3) ∧
    (nativeProjection C i).sg = true) ∧
  EmptyCandidates (fun i => NativeCand.ofAgent (C i))

/-- The candidate-zero conjunct does produce an honest generated
H_cand origin once the native clean singleton conjuncts hold. -/
theorem referencePreparation_prepared_has_candidate_history
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (h : ReferencePreparationPreparedCore ring C) :
    H_cand ring (fun i => NativeCand.ofAgent (C i)) := by
  rcases h with ⟨_, _, hone, hclean, _, hempty⟩
  apply H_cand_origin ring (fun i => NativeCand.ofAgent (C i))
  refine ⟨?_, ?_, ?_⟩
  · change OneNativeLeader (nativeProjection C)
    exact hone
  · change C_native ring (nativeProjection C)
    exact hclean
  · intro i
    have hzero : (NativeCand.ofAgent (C i)).candidate =
        zeroCandidate := hempty i
    change (NativeCand.ofAgent (C i)).candidate.alpha = false ∧
      (NativeCand.ofAgent (C i)).candidate.m = false ∧
      ((NativeCand.ofAgent (C i)).native.l = true →
        (NativeCand.ofAgent (C i)).candidate.C = false)
    rw [hzero]
    exact ⟨rfl, rfl, fun _ => rfl⟩

/-- A proper nonzero clockwise offset is not the original site.
The proof uses the literal PPL.shiftRight modular formula. -/
theorem referencePreparation_sealed_site_ne {n : Nat}
    (ring : DirectedRing n) (a : Fin n) (d : Nat)
    (hd : 0 < d) (hdn : d < n) :
    sealedSite ring a d ≠ a := by
  intro h
  have hv := congrArg Fin.val h
  change (a.val + d) % n = a.val at hv
  by_cases hlt : a.val + d < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have hge : n ≤ a.val + d := by omega
    have hmodlt : a.val + d - n < n := by omega
    rw [Nat.mod_eq_sub_mod hge,
      Nat.mod_eq_of_lt hmodlt] at hv
    omega

/-- The sealed_prep_expected start requires two distinct leader
sites. A singleton cannot satisfy ConsecutiveNative for d in (0,n).
The missing "field" is not an unrecorded flag: a second leader
would contradict the singleton cut itself. -/
theorem referencePreparation_singleton_not_consecutive {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat)
    (hsingle : OneNativeLeader N)
    (hconsecutive : ConsecutiveNative ring N a b d) : False := by
  obtain ⟨root, _, hunique⟩ := hsingle
  rcases hconsecutive with ⟨hd, hdn, hb, ha, hlast, _⟩
  have hab : a = b :=
    (hunique a ha).trans (hunique b hlast).symm
  have heq : sealedSite ring a d = a :=
    hb.symm.trans hab.symm
  exact (referencePreparation_sealed_site_ne ring a d
    (by omega : 0 < d) hdn) heq

/-- On a singleton, the sealed target holds already at time zero
whenever the chosen two endpoints are distinct: at least one of
the two specified leader bits is false. This is not preparation. -/
theorem referencePreparation_singleton_sealed_target
    {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (a b : Fin n) (d : Nat)
    (hsingle : OneNativeLeader N) (hne : a ≠ b) :
    SealedPrepTarget ring a b d N := by
  obtain ⟨root, _, hunique⟩ := hsingle
  cases ha : (N a).l with
  | false =>
      exact Or.inl ha
  | true =>
      have hnot : b ≠ root := by
        intro hb
        apply hne
        exact (hunique a ha).trans hb.symm
      cases hb : (N b).l with
      | false =>
          exact Or.inr (Or.inl hb)
      | true =>
          exact False.elim (hnot (hunique b hb))

/-- Exact native start of the existing sealed preparation theorem,
strengthened only by the grant-free physical-cut condition. -/
def ReferencePreparationSealedStart {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (C : HeadlineConfiguration n) : Prop :=
  P ring (nativeProjection C) ∧
  ConsecutiveNative ring (nativeProjection C) a b d ∧
  NativeLiftGrantFree C

/-- The actually transferable physical stopping class. This includes
the bad cut where a grant reappears; it is NOT the paper's prepared
native/candidate class. -/
def ReferencePreparationSealedExit {n : Nat}
    (ring : DirectedRing n) (a b : Fin n) (d : Nat)
    (C : HeadlineConfiguration n) : Prop :=
  NativeLiftGrantStop (SealedPrepTarget ring a b d) C

/-- The paper singleton is incompatible with the sealed start,
even when all its native and grant-free hypotheses are kept. -/
theorem referencePreparation_singleton_not_sealed_start
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (a b : Fin n) (d : Nat)
    (hsingle : ReferencePreparationSingletonCore ring C) :
    ¬ ReferencePreparationSealedStart ring a b d C := by
  intro hstart
  exact referencePreparation_singleton_not_consecutive ring
    (nativeProjection C) a b d hsingle.2.2 hstart.2.1

/-- If one artificially keeps the two sealed endpoints at a proper
distance, the singleton is already in SealedPrepTarget, hence in
the stopped physical exit target, without completing sigma_p. -/
theorem referencePreparation_singleton_already_sealed_exit
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (a b : Fin n) (d : Nat)
    (hd : 0 < d) (hdn : d < n)
    (hb : b = sealedSite ring a d)
    (hsingle : ReferencePreparationSingletonCore ring C) :
    ReferencePreparationSealedExit ring a b d C := by
  have hne : a ≠ b := by
    intro heq
    exact (referencePreparation_sealed_site_ne ring a d hd hdn)
      (hb.symm.trans heq.symm)
  exact Or.inl
    (referencePreparation_singleton_sealed_target ring
      (nativeProjection C) a b d hsingle.2.2 hne)

/-- SealedPrep supplies 3*n*d, not 5*n^2+n/2.
For d<n, it is (non-sharply) dominated by the headline 6*n^2
charge. This inequality alone does not reconcile start/target. -/
theorem referencePreparation_sealed_budget_le
    (n d : Nat) (hdn : d < n) :
    3 * n * d ≤ 6 * n ^ 2 := by
  calc
    3 * n * d ≤ (3 * n) * n :=
      Nat.mul_le_mul_left (3 * n) (Nat.le_of_lt hdn)
    _ = 3 * n ^ 2 := by
      simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
      ac_rfl
    _ ≤ 6 * n ^ 2 :=
      Nat.mul_le_mul_right (n ^ 2) (by omega)

/-- Pure-native corollary of sealed_prep_expected with the larger
headline coefficient. Still a two-leader statement. -/
theorem referencePreparation_native_sealed_to_six {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (a b : Fin n) (d : Nat)
    (hd : 0 < d) (hdn : d < n)
    (N : Fin n → CertNative)
    (hP : P ring N)
    (hconsecutive : ConsecutiveNative ring N a b d) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (nativeE ring) (SealedPrepTarget ring a b d)
      N ((6 * n ^ 2 : Nat) : Rat) := by
  have hnative :=
    sealed_prep_expected hn ring a b d hd hdn N hP hconsecutive
  have hcost :=
    (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (nativeE ring) (SealedPrepTarget ring a b d)
      (by omega : 0 < n) N (3 * n * d)).1 hnative
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (nativeE ring) (SealedPrepTarget ring a b d)
    (by omega : 0 < n) N (6 * n ^ 2)).2
  intro T
  exact Nat.le_trans (hcost T)
    (Nat.mul_le_mul_left (n ^ T)
      (referencePreparation_sealed_budget_le n d hdn))

/-- A formally valid StageReferencePreparation instance using the
ACTUAL physical stepper, but with the sealed TWO-LEADER start and
the STOP-ON-REGRANT exit. It is intentionally NOT the requested
paper sigma_1 -> sigma_p instance. This is the maximal direct
transfer of sealed_prep_expected and native_lift_grant_stopped_cost_le. -/
theorem referencePreparation_physical_sealed_first_exit
    {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (a b : Fin n) (d : Nat)
    (hd : 0 < d) (hdn : d < n) :
    StageReferencePreparation (headlinePhysicalNext ring)
      (ReferencePreparationSealedStart ring a b d)
      (ReferencePreparationSealedExit ring a b d) := by
  intro C hstart
  have hnative :=
    sealed_prep_expected hn ring a b d hd hdn
      (nativeProjection C) hstart.1 hstart.2.1
  have hcost :=
    (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (nativeE ring) (SealedPrepTarget ring a b d)
      (by omega : 0 < n) (nativeProjection C)
      (3 * n * d)).1 hnative
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (headlinePhysicalNext ring)
    (ReferencePreparationSealedExit ring a b d)
    (by omega : 0 < n) C (6 * n ^ 2)).2
  intro T
  exact Nat.le_trans
    (native_lift_grant_stopped_cost_le
      (by omega : 3 ≤ n) ring
      (SealedPrepTarget ring a b d) C T)
    (Nat.le_trans (hcost T)
      (Nat.mul_le_mul_left (n ^ T)
        (referencePreparation_sealed_budget_le n d hdn)))

end L3

/-!
Native singleton preparation, scheduler-clock certificates.

These lemmas separate three genuine ingredients
from the six physical handoff obligations which remain open:
the fixed unique leader under nativeE, the predictable ordered-edge
clock, and the exact two-incident-edge clock. No assertion that an
ordered sweep has already retired a physical bullet is inferred
merely from completion of its scheduler tags.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The native half of the paper's prepared target at the ORIGINAL
singleton root: exactly that one leader, no bullet of either kind,
and every native signal one. Candidate zeros belong to a separate
physical-history obligation. -/
def ReferencePreparationNativePreparedAt {n : Nat}
    (root : Fin n) (N : TripleNativeState n) : Prop :=
  (N root).l = true ∧
  (∀ i : Fin n, (N i).l = true → i = root) ∧
  (∀ i : Fin n,
    (N i).b = (0 : Fin 3) ∧ (N i).sg = true)

theorem referencePreparationNativePreparedHasSingleton {n : Nat}
    (root : Fin n) (N : TripleNativeState n)
    (h : ReferencePreparationNativePreparedAt root N) :
    OneNativeLeader N := by
  exact ⟨root, h.1, h.2.1⟩

/-- A PPlus singleton has the same original leader after every
nativeE scheduler word, regardless of the bullet and signal fields.
This uses the genuine E-row non-creation and PPlus preservation,
not the two-leader SealedPrep start. -/
theorem referencePreparationNativeSingletonRootWord {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n) (root : Fin n) :
    ∀ (w : List (Fin n)) (N : TripleNativeState n),
      (N root).l = true →
      (∀ i : Fin n, (N i).l = true → i = root) →
      PPlus ring N →
      (nativeLiftNativeRun ring N w root).l = true ∧
      (∀ i : Fin n,
        (nativeLiftNativeRun ring N w i).l = true → i = root) ∧
      PPlus ring (nativeLiftNativeRun ring N w) := by
  intro w
  induction w with
  | nil =>
      intro N hroot hunique hplus
      exact ⟨hroot, hunique, hplus⟩
  | cons e es ih =>
      intro N hroot hunique hplus
      have hfixed := CandidateNativeProof.leader_fixed
        (by omega : 3 ≤ n) ring N e root hroot hunique hplus
      have hnext := nativeE_preserves_PPlus
        (by omega : 3 ≤ n) ring N e hplus
      exact ih (nativeE ring N e) hfixed.1 hfixed.2.1 hnext

/-- Proof-only nativeE plus an ordered list of scheduler edges.
Each edge at the head must be observed after the previous head:
the scheduler may choose arbitrary other edges in between.
The native configuration ALWAYS takes the actual nativeE step. -/
abbrev ReferencePreparationNamedState (n : Nat) :=
  TripleNativeState n × List (Fin n)

def referencePreparationNamedStep {n : Nat}
    (ring : DirectedRing n)
    (z : ReferencePreparationNamedState n) (e : Fin n) :
    ReferencePreparationNamedState n :=
  (nativeE ring z.1 e,
    match z.2 with
    | [] => []
    | f :: fs => if e = f then fs else f :: fs)

def referencePreparationNamedDone {n : Nat}
    (z : ReferencePreparationNamedState n) : Prop :=
  z.2 = []

def referencePreparationNamedQuota {n : Nat}
    (z : ReferencePreparationNamedState n) : Nat :=
  z.2.length

def referencePreparationNamedEdge {n : Nat}
    (root : Fin n) (z : ReferencePreparationNamedState n) : Fin n :=
  match z.2 with
  | [] => root
  | f :: _ => f

theorem referencePreparationNamedNativeStep {n : Nat}
    (ring : DirectedRing n)
    (z : ReferencePreparationNamedState n) (e : Fin n) :
    (referencePreparationNamedStep ring z e).1 =
      nativeE ring z.1 e := by
  rfl

/-- Real native projection throughout every clock word, including
all intervening non-nominated services. -/
theorem referencePreparationNamedNativeRun {n : Nat}
    (ring : DirectedRing n) :
    ∀ (w : List (Fin n))
      (z : ReferencePreparationNamedState n),
      (LDSinkBoundedKernel.run
        (referencePreparationNamedStep ring) z w).1 =
      nativeLiftNativeRun ring z.1 w := by
  intro w
  induction w with
  | nil =>
      intro z
      rfl
  | cons e es ih =>
      intro z
      change (LDSinkBoundedKernel.run
          (referencePreparationNamedStep ring)
          (referencePreparationNamedStep ring z e) es).1 =
        nativeLiftNativeRun ring (nativeE ring z.1 e) es
      exact ih (referencePreparationNamedStep ring z e)

/-- Servicing the currently nominated head removes exactly one
proof-only clock tag, never a native physical bullet tag. -/
theorem referencePreparationNamedDrop {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ReferencePreparationNamedState n)
    (h : ¬ referencePreparationNamedDone z) :
    referencePreparationNamedQuota
        (referencePreparationNamedStep ring z
          (referencePreparationNamedEdge root z)) + 1 ≤
      referencePreparationNamedQuota z := by
  rcases z with ⟨N, es⟩
  cases es with
  | nil =>
      exact False.elim (h rfl)
  | cons f fs =>
      simp [referencePreparationNamedQuota,
        referencePreparationNamedStep,
        referencePreparationNamedEdge]

/-- Every other physical service either consumes the head or
keeps the exact pending-list length. -/
theorem referencePreparationNamedNonincrease {n : Nat}
    (ring : DirectedRing n)
    (z : ReferencePreparationNamedState n)
    (_h : ¬ referencePreparationNamedDone z) (e : Fin n) :
    referencePreparationNamedQuota
      (referencePreparationNamedStep ring z e) ≤
        referencePreparationNamedQuota z := by
  rcases z with ⟨N, es⟩
  cases es with
  | nil =>
      simp [referencePreparationNamedQuota,
        referencePreparationNamedStep]
  | cons f fs =>
      by_cases hf : e = f
      · simp [referencePreparationNamedQuota,
          referencePreparationNamedStep, hf]
      · simp [referencePreparationNamedQuota,
          referencePreparationNamedStep, hf]

/-- An ordered list of k actual scheduler edges has mean at most
n*k, in the exact finite-horizon costNumerator form. The clock
carrier includes and executes the real birth-free native state. -/
theorem referencePreparationNamedClockCost {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n) (edges : List (Fin n)) (T : Nat) :
    costNumerator (referencePreparationNamedStep ring)
      referencePreparationNamedDone (N, edges) T ≤
        n ^ T * (n * edges.length) := by
  exact Prob.costNumerator_le_of_nominated_edge
    (referencePreparationNamedStep ring)
    referencePreparationNamedDone
    referencePreparationNamedQuota
    (referencePreparationNamedEdge root)
    (referencePreparationNamedDrop ring root)
    (referencePreparationNamedNonincrease ring)
    (N, edges) T

/-- The order e_0,...,e_(n-1) from the paper. This is a
scheduler-list clock, not yet a physical old-label certificate. -/
def referencePreparationForwardEdges {n : Nat}
    (ring : DirectedRing n) (root : Fin n) : List (Fin n) :=
  List.ofFn (fun i : Fin n => PPL.shiftRight ring root i.val)

/-- The order e_(n-1),...,e_0 for backward signal return. -/
def referencePreparationBackwardEdges {n : Nat}
    (ring : DirectedRing n) (root : Fin n) : List (Fin n) :=
  (referencePreparationForwardEdges ring root).reverse

theorem referencePreparationForwardClockCost {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n) (T : Nat) :
    costNumerator (referencePreparationNamedStep ring)
      referencePreparationNamedDone
      (N, referencePreparationForwardEdges ring root) T ≤
        n ^ T * n ^ 2 := by
  have h := referencePreparationNamedClockCost ring root N
    (referencePreparationForwardEdges ring root) T
  have hlen : (referencePreparationForwardEdges ring root).length =
      n := by
    simp only [referencePreparationForwardEdges, List.length_ofFn]
  rw [hlen] at h
  have hsquare : n * n = n ^ 2 := by
    rw [Nat.pow_two]
  rw [hsquare] at h
  exact h

theorem referencePreparationBackwardClockCost {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n) (T : Nat) :
    costNumerator (referencePreparationNamedStep ring)
      referencePreparationNamedDone
      (N, referencePreparationBackwardEdges ring root) T ≤
        n ^ T * n ^ 2 := by
  have h := referencePreparationNamedClockCost ring root N
    (referencePreparationBackwardEdges ring root) T
  have hlen : (referencePreparationBackwardEdges ring root).length =
      n := by
    simp only [referencePreparationBackwardEdges,
      List.length_reverse, referencePreparationForwardEdges,
      List.length_ofFn]
  rw [hlen] at h
  have hsquare : n * n = n ^ 2 := by
    rw [Nat.pow_two]
  rw [hsquare] at h
  exact h

/-- The first incident service has two nominated edges.
The Boolean is an absorbing proof-only history marker. -/
def referencePreparationIncidentFlagStep {n : Nat}
    (a b : Fin n) (seen : Bool) (e : Fin n) : Bool :=
  if e = a then true else if e = b then true else seen

private theorem referencePreparationIncidentFlagTrueCost {n : Nat}
    (a b : Fin n) (T : Nat) :
    costNumerator (referencePreparationIncidentFlagStep a b)
      (fun seen : Bool => seen = true) true T = 0 := by
  classical
  cases T with
  | zero =>
      rfl
  | succ U =>
      exact costNumerator_terminal
        (referencePreparationIncidentFlagStep a b)
        (fun seen : Bool => seen = true) true rfl (U + 1)

/-- Exact half-speed finite-horizon bound, without rounding n/2
up to an integer. Both distinct incident edges each carry one
unit of stopping mass at every still-active scheduler cut. -/
theorem referencePreparationIncidentFlagHalfCost {n : Nat}
    (hn : 2 ≤ n) (a b : Fin n) (hab : a ≠ b) :
    ∀ T : Nat,
      2 * costNumerator (referencePreparationIncidentFlagStep a b)
        (fun seen : Bool => seen = true) false T ≤ n ^ T * n := by
  classical
  intro T
  induction T with
  | zero =>
      simp only [costNumerator_zero, Nat.mul_zero]
      exact Nat.zero_le _
  | succ T ih =>
      have hnot : ¬ ((fun seen : Bool => seen = true) false) := by
        intro h
        cases h
      have hchild (e : Fin n) :
          costNumerator (referencePreparationIncidentFlagStep a b)
              (fun seen : Bool => seen = true)
              (referencePreparationIncidentFlagStep a b false e) T =
            (if e = a then 0
             else if e = b then 0
             else costNumerator (referencePreparationIncidentFlagStep a b)
               (fun seen : Bool => seen = true) false T) := by
        by_cases ha : e = a
        · simp [referencePreparationIncidentFlagStep, ha,
            referencePreparationIncidentFlagTrueCost a b T]
        · by_cases hb : e = b
          · simp [referencePreparationIncidentFlagStep, ha, hb,
              referencePreparationIncidentFlagTrueCost a b T]
          · simp [referencePreparationIncidentFlagStep, ha, hb]
      have hsum :
          (List.ofFn (fun e : Fin n =>
            costNumerator (referencePreparationIncidentFlagStep a b)
              (fun seen : Bool => seen = true)
              (referencePreparationIncidentFlagStep a b false e) T)).sum =
          (n - 2) *
            costNumerator (referencePreparationIncidentFlagStep a b)
              (fun seen : Bool => seen = true) false T := by
        calc
          _ = (List.ofFn (fun e : Fin n =>
                if e = a then 0
                else if e = b then 0
                else costNumerator
                  (referencePreparationIncidentFlagStep a b)
                  (fun seen : Bool => seen = true) false T)).sum :=
            ofFn_sum_eq _ _ hchild
          _ = 0 + 0 + (n - 2) *
                costNumerator (referencePreparationIncidentFlagStep a b)
                  (fun seen : Bool => seen = true) false T :=
            tagged_long_ofFn_two_edge_sum hn a b 0 0 _ hab
          _ = (n - 2) *
                costNumerator (referencePreparationIncidentFlagStep a b)
                  (fun seen : Bool => seen = true) false T := by
            omega
      have hrec :
          costNumerator (referencePreparationIncidentFlagStep a b)
              (fun seen : Bool => seen = true) false (T + 1) =
            n ^ (T + 1) + (n - 2) *
              costNumerator (referencePreparationIncidentFlagStep a b)
                (fun seen : Bool => seen = true) false T := by
        rw [costNumerator_succ
          (referencePreparationIncidentFlagStep a b)
          (fun seen : Bool => seen = true) false hnot T, hsum]
      have hsplit : 2 + (n - 2) = n := by omega
      calc
        2 * costNumerator (referencePreparationIncidentFlagStep a b)
            (fun seen : Bool => seen = true) false (T + 1) =
          2 * n ^ (T + 1) + (n - 2) *
            (2 * costNumerator (referencePreparationIncidentFlagStep a b)
              (fun seen : Bool => seen = true) false T) := by
                rw [hrec, Nat.mul_add]
                ac_rfl
        _ ≤ 2 * n ^ (T + 1) + (n - 2) * (n ^ T * n) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left (n - 2) ih) _
        _ = n ^ (T + 1) * n := by
          calc
            _ = (2 + (n - 2)) * (n ^ T * n) := by
              rw [Nat.add_mul, Nat.pow_succ]
            _ = n ^ (T + 1) * n := by
              rw [hsplit, Nat.pow_succ]
              ac_rfl

/-- Add an independent nativeE history component to the two-port
first-hit marker; this is the actual birth-free native scheduler. -/
def referencePreparationIncidentNativeStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : Bool × TripleNativeState n) (e : Fin n) :
    Bool × TripleNativeState n :=
  (referencePreparationIncidentFlagStep root
      (ring.leftNeighbor root) z.1 e,
    nativeE ring z.2 e)

private theorem referencePreparationLeftNeighborNe
    {n : Nat} (ring : DirectedRing n) (hn2 : 2 ≤ n)
    (x : Fin n) :
    ring.leftNeighbor x ≠ x := by
  intro h
  have hv := congrArg Fin.val h
  change (x.val + n - 1) % n = x.val at hv
  rcases Nat.eq_zero_or_pos x.val with h0 | hpos
  · have h1 : (x.val + n - 1) % n = n - 1 := by
      rw [h0, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, h0] at hv
    omega
  · have h1 : (x.val + n - 1) % n = x.val - 1 := by
      rw [show x.val + n - 1 = (x.val - 1) + n by omega,
        Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1] at hv
    omega

theorem referencePreparationIncidentNativeHalfCost {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n) (T : Nat) :
    2 * costNumerator (referencePreparationIncidentNativeStep ring root)
      (fun z : Bool × TripleNativeState n => z.1 = true)
      (false, N) T ≤ n ^ T * n := by
  have hports : root ≠ ring.leftNeighbor root := by
    exact Ne.symm
      (referencePreparationLeftNeighborNe
        ring (by omega : 2 ≤ n) root)
  have hproj :
      ∀ (z : Bool × TripleNativeState n) (e : Fin n),
        (referencePreparationIncidentNativeStep ring root z e).1 =
          referencePreparationIncidentFlagStep root
            (ring.leftNeighbor root) z.1 e := by
    intro z e
    rfl
  have hcost := Prob.costNumerator_ghost_eq
    (referencePreparationIncidentFlagStep root
      (ring.leftNeighbor root))
    (referencePreparationIncidentNativeStep ring root)
    hproj (fun seen : Bool => seen = true) (false, N) T
  rw [hcost]
  exact referencePreparationIncidentFlagHalfCost
    (by omega : 2 ≤ n) root (ring.leftNeighbor root) hports T

/-- The six paper budgets (five n^2 stages, one n/2 stage)
fit the larger 6n^2 envelope for n >= 5, in doubled integer
form so the half-step is not silently rounded. -/
theorem referencePreparationSixBudget (n : Nat) (hn : 5 ≤ n) :
    10 * n ^ 2 + n ≤ 12 * n ^ 2 := by
  have hle : n ≤ n ^ 2 := by
    calc
      n = n * 1 := by simp
      _ ≤ n * n := Nat.mul_le_mul_left n (by omega)
      _ = n ^ 2 := by rw [Nat.pow_two]
  calc
    10 * n ^ 2 + n ≤ 10 * n ^ 2 + n ^ 2 :=
      Nat.add_le_add_left hle _
    _ ≤ 12 * n ^ 2 := by omega

/-- Explicit six-stage strong-Markov *conditional* consumer.
Each A/B/C/D/E predicate must be certified at its true
revealed-history first cut by its own physical stage theorem.
This lemma composes those hypothetical nativeE clocks with no
independence assumption; it does NOT discharge their hypotheses. -/
theorem referencePreparationSixStageCostOfCuts {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (A B C D E P : TripleNativeState n → Prop)
    (hfirst : ∀ T,
      costNumerator (nativeE ring) (fun z => A z ∨ P z) N T ≤
        n ^ T * n ^ 2)
    (hsecond : ∀ z, A z → ∀ T,
      costNumerator (nativeE ring) (fun x => B x ∨ P x) z T ≤
        n ^ T * n ^ 2)
    (hthird : ∀ z, B z → ∀ T,
      costNumerator (nativeE ring) (fun x => C x ∨ P x) z T ≤
        n ^ T * n ^ 2)
    (hfourth : ∀ z, C z → ∀ T,
      costNumerator (nativeE ring) (fun x => D x ∨ P x) z T ≤
        n ^ T * n ^ 2)
    (hfifth : ∀ z, D z → ∀ T,
      costNumerator (nativeE ring) (fun x => E x ∨ P x) z T ≤
        n ^ T * n ^ 2)
    (hsixth : ∀ z, E z → ∀ T,
      costNumerator (nativeE ring) P z T ≤ n ^ T * n ^ 2) :
    ∀ T, costNumerator (nativeE ring) P N T ≤
      n ^ T * (6 * n ^ 2) := by
  have hD : ∀ z, D z → ∀ T,
      costNumerator (nativeE ring) P z T ≤
        n ^ T * (2 * n ^ 2) := by
    intro z hz T
    have h := Prob.costNumerator_stage_le
      (nativeE ring) z E P (n ^ 2) (n ^ 2)
      (hfifth z hz) hsixth T
    have heq : n ^ 2 + n ^ 2 = 2 * n ^ 2 := by omega
    rw [heq] at h
    exact h
  have hC : ∀ z, C z → ∀ T,
      costNumerator (nativeE ring) P z T ≤
        n ^ T * (3 * n ^ 2) := by
    intro z hz T
    have h := Prob.costNumerator_stage_le
      (nativeE ring) z D P (n ^ 2) (2 * n ^ 2)
      (hfourth z hz) hD T
    have heq : n ^ 2 + 2 * n ^ 2 = 3 * n ^ 2 := by omega
    rw [heq] at h
    exact h
  have hB : ∀ z, B z → ∀ T,
      costNumerator (nativeE ring) P z T ≤
        n ^ T * (4 * n ^ 2) := by
    intro z hz T
    have h := Prob.costNumerator_stage_le
      (nativeE ring) z C P (n ^ 2) (3 * n ^ 2)
      (hthird z hz) hC T
    have heq : n ^ 2 + 3 * n ^ 2 = 4 * n ^ 2 := by omega
    rw [heq] at h
    exact h
  have hA : ∀ z, A z → ∀ T,
      costNumerator (nativeE ring) P z T ≤
        n ^ T * (5 * n ^ 2) := by
    intro z hz T
    have h := Prob.costNumerator_stage_le
      (nativeE ring) z B P (n ^ 2) (4 * n ^ 2)
      (hsecond z hz) hB T
    have heq : n ^ 2 + 4 * n ^ 2 = 5 * n ^ 2 := by omega
    rw [heq] at h
    exact h
  intro T
  have h := Prob.costNumerator_stage_le
    (nativeE ring) N A P (n ^ 2) (5 * n ^ 2)
    hfirst hA T
  have heq : n ^ 2 + 5 * n ^ 2 = 6 * n ^ 2 := by omega
  rw [heq] at h
  exact h

end L3

/-!
Initial native-bullet ancestry and ordered sweep.

A label is a proof-only Boolean attached to a bullet at the
singleton cut. On nativeE it is deleted at the selected source;
at the responder it is retained only if the OLD responder bullet
was not overwritten, or inherited from a truly transported OLD
source bullet. The actual new bullet is checked in both cases.
A fresh firing has no label, collision loses the incoming label,
and a bullet entering the fixed leader does not acquire a label.

All new functions are proof-only and use the original nativeE
scheduler, not the production protocol's birth rule.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The old native bullet at a cut is provisionally labeled.
Both live bullets (2) and dummy bullets (1) are included. -/
def referencePreparationInitialOldLabels {n : Nat}
    (N : TripleNativeState n) (i : Fin n) : Bool :=
  if (N i).b = (0 : Fin 3) then false else true

/-- An OLD label may be attached only to an occupied native site. -/
def ReferencePreparationLabelSound {n : Nat}
    (N : TripleNativeState n) (mask : Fin n → Bool) : Prop :=
  ∀ i : Fin n, mask i = true → (N i).b ≠ (0 : Fin 3)

/-- Every actual initial bullet, including a dummy, gets its label.
There is no inference of old ancestry from a later newly fired
bullet of the same numerical kind. -/
theorem referencePreparationInitialOldLabelsSound {n : Nat}
    (N : TripleNativeState n) :
    ReferencePreparationLabelSound N
      (referencePreparationInitialOldLabels N) := by
  intro i hi
  by_cases hz : (N i).b = (0 : Fin 3)
  · have hfalse :
        referencePreparationInitialOldLabels N i = false := by
      simp [referencePreparationInitialOldLabels, hz]
    rw [hfalse] at hi
    cases hi
  · exact hz

/-- The label update is a one-way OLD ancestry rule. At a selected
source no label survives. At the responder the OLD resident is
retained only when it did not fire; alternatively an old source
label crosses to an empty nonleader responder only when the OLD
source did not fire. A post-E nonempty bullet is required in
either case, so a deleted or overwritten label cannot reappear.
No other site changes its label. -/
noncomputable def referencePreparationOldLabelStep {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (mask : Fin n → Bool) (e : Fin n) (i : Fin n) : Bool :=
  if i = e then false
  else if i = ring.rightNeighbor e then
    if (nativeE ring N e i).b ≠ (0 : Fin 3) ∧
        ((mask i = true ∧
            ¬ ((N i).l = true ∧ (N i).sg = true)) ∨
         (mask e = true ∧ (N e).b ≠ (0 : Fin 3) ∧
            ¬ ((N e).l = true ∧ (N e).sg = true) ∧
            (N i).l = false ∧
            (N i).b = (0 : Fin 3)))
    then true else false
  else mask i

/-- A selected nativeE initiator loses its old label, including
when a firing immediately creates a *new*, unlabelled bullet. -/
theorem referencePreparationOldLabelSource {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (mask : Fin n → Bool) (e : Fin n) :
    referencePreparationOldLabelStep ring N mask e e = false := by
  simp only [referencePreparationOldLabelStep, if_pos rfl, ↓reduceIte]

/-- The labels of every nonincident agent have the exact physical
nativeE frame; a new label cannot appear at an unrelated site. -/
theorem referencePreparationOldLabelFrame {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (mask : Fin n → Bool) (e i : Fin n)
    (he : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    referencePreparationOldLabelStep ring N mask e i =
      mask i := by
  simp only [referencePreparationOldLabelStep,
    if_neg he, if_neg hj]

/-- The selected responder has precisely the old-resident-or-
transported-source Boolean formula, guarded by its real post-E
bullet. This formula decides collision and firing overwrite. -/
theorem referencePreparationOldLabelResponder {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (mask : Fin n → Bool) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    referencePreparationOldLabelStep ring N mask e
        (ring.rightNeighbor e) =
      (if (nativeE ring N e (ring.rightNeighbor e)).b ≠
            (0 : Fin 3) ∧
          ((mask (ring.rightNeighbor e) = true ∧
              ¬ ((N (ring.rightNeighbor e)).l = true ∧
                 (N (ring.rightNeighbor e)).sg = true)) ∨
           (mask e = true ∧ (N e).b ≠ (0 : Fin 3) ∧
              ¬ ((N e).l = true ∧ (N e).sg = true) ∧
              (N (ring.rightNeighbor e)).l = false ∧
              (N (ring.rightNeighbor e)).b = (0 : Fin 3)))
        then true else false) := by
  have he : ring.rightNeighbor e ≠ e := hne
  simp only [referencePreparationOldLabelStep,
    if_neg he, if_pos rfl, ↓reduceIte]

/-- All labels continue to ride genuine nonempty native bullets.
This does not assume PPlus: the post-output occupancy is built
directly into the cut-label transfer rule. -/
theorem referencePreparationOldLabelSoundStep {n : Nat}
    (ring : DirectedRing n) (N : TripleNativeState n)
    (mask : Fin n → Bool) (e : Fin n)
    (hs : ReferencePreparationLabelSound N mask) :
    ReferencePreparationLabelSound (nativeE ring N e)
      (referencePreparationOldLabelStep ring N mask e) := by
  intro i hi
  by_cases he : i = e
  · have hh := referencePreparationOldLabelSource ring N mask e
    rw [he, hh] at hi
    cases hi
  · by_cases hj : i = ring.rightNeighbor e
    · have hcondition :
          (nativeE ring N e i).b ≠ (0 : Fin 3) ∧
            ((mask i = true ∧
                ¬ ((N i).l = true ∧ (N i).sg = true)) ∨
              (mask e = true ∧ (N e).b ≠ (0 : Fin 3) ∧
                ¬ ((N e).l = true ∧ (N e).sg = true) ∧
                (N i).l = false ∧
                (N i).b = (0 : Fin 3))) := by
        by_cases hh :
            (nativeE ring N e i).b ≠ (0 : Fin 3) ∧
              ((mask i = true ∧
                  ¬ ((N i).l = true ∧ (N i).sg = true)) ∨
                (mask e = true ∧ (N e).b ≠ (0 : Fin 3) ∧
                  ¬ ((N e).l = true ∧ (N e).sg = true) ∧
                  (N i).l = false ∧
                  (N i).b = (0 : Fin 3)))
        · exact hh
        · have hfalse :
              referencePreparationOldLabelStep ring N mask e i =
                false := by
            simp only [referencePreparationOldLabelStep,
              if_neg he, if_pos hj, if_neg hh]
          rw [hfalse] at hi
          cases hi
      exact hcondition.1
    · have hframe :
          nativeE ring N e i = N i := by
        simp only [nativeE, if_neg he, if_neg hj]
      rw [hframe]
      have hold :=
        referencePreparationOldLabelFrame ring N mask e i he hj
      rw [hold] at hi
      exact hs i hi

/-- A prefix of sites is a closed ancestry barrier whenever every
incoming edge either starts inside the prefix or ends at its
unique leader. This is the one-step core of H.2: no counterclockwise
transport can create a new old label inside the protected prefix. -/
theorem referencePreparationOldLabelsClosedStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n) (mask : Fin n → Bool)
    (e : Fin n) (S : Fin n → Prop)
    (hroot : (N root).l = true)
    (hboundary : ∀ i f : Fin n,
      S i → ring.rightNeighbor f = i → S f ∨ i = root)
    (hcleared : ∀ i : Fin n, S i → mask i = false) :
    ∀ i : Fin n, S i →
      referencePreparationOldLabelStep ring N mask e i = false := by
  intro i hi
  by_cases he : i = e
  · rw [he]
    exact referencePreparationOldLabelSource ring N mask e
  · by_cases hj : i = ring.rightNeighbor e
    · rcases hboundary i e hi hj.symm with hsource | hleader
      · have hezero := hcleared e hsource
        have hizero := hcleared i hi
        simp only [referencePreparationOldLabelStep,
          if_neg he, if_pos hj, if_neg (show
            ¬ ((nativeE ring N e i).b ≠ (0 : Fin 3) ∧
              ((mask i = true ∧
                ¬ ((N i).l = true ∧ (N i).sg = true)) ∨
               (mask e = true ∧ (N e).b ≠ (0 : Fin 3) ∧
                ¬ ((N e).l = true ∧ (N e).sg = true) ∧
                (N i).l = false ∧ (N i).b = (0 : Fin 3)))) from by
                  intro hbad
                  rcases hbad.2 with hstay | hmove
                  · rw [hizero] at hstay
                    cases hstay.1
                  · rw [hezero] at hmove
                    cases hmove.1)]
      · have hizero := hcleared i hi
        have hir : (N i).l = true := by
          rw [hleader]
          exact hroot
        simp only [referencePreparationOldLabelStep,
          if_neg he, if_pos hj, if_neg (show
            ¬ ((nativeE ring N e i).b ≠ (0 : Fin 3) ∧
              ((mask i = true ∧
                ¬ ((N i).l = true ∧ (N i).sg = true)) ∨
               (mask e = true ∧ (N e).b ≠ (0 : Fin 3) ∧
                ¬ ((N e).l = true ∧ (N e).sg = true) ∧
                (N i).l = false ∧ (N i).b = (0 : Fin 3)))) from by
                  intro hbad
                  rcases hbad.2 with hstay | hmove
                  · rw [hizero] at hstay
                    cases hstay.1
                  · rw [hir] at hmove
                    cases hmove.2.2.2.1)]
    · rw [referencePreparationOldLabelFrame ring N mask e i he hj]
      exact hcleared i hi

/-- The unique fixed root cannot be recolonized by a labeled
pre-cut bullet on an incoming edge: such a bullet is absorbed
by the OLD leader rather than transported through it. -/
theorem referencePreparationOldLabelRootClosed {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (N : TripleNativeState n) (mask : Fin n → Bool)
    (hroot : (N root).l = true)
    (hzero : mask root = false) :
    referencePreparationOldLabelStep ring N mask e root = false := by
  exact referencePreparationOldLabelsClosedStep
    ring root N mask e (fun i => i = root) hroot
    (by
      intro i f hi hf
      exact Or.inr hi)
    (by
      intro i hi
      rw [hi]
      exact hzero)
    root rfl


end L3

/-!
Clockwise old-bullet ancestry barrier and an adapted
first-cut clock.

The chronological state below is a proof-only nativeE decoration:
native state, inherited-bullet Boolean mask, and the index of the
next clockwise edge to be nominated. It neither changes nativeE nor
interprets a fresh firing as an inherited bullet. In contrast with
the existing pending-list clock, the cursor implementation lets the
closed-prefix condition be stated directly at every scheduler word.

The final theorem is a conditional six-stage CONSUMER. Only its first
stage is discharged here. The remaining stage hypotheses
are not hidden or inferred from old-label extinction.
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

private theorem referencePreparationShiftZero {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    PPL.shiftRight ring root 0 = root := by
  apply Fin.ext
  simp only [PPL.shiftRight, Nat.add_zero]
  exact Nat.mod_eq_of_lt root.isLt

private theorem referencePreparationShiftSucc {n : Nat}
    (ring : DirectedRing n) (root : Fin n) (k : Nat) :
    PPL.shiftRight ring root (k + 1) =
      ring.rightNeighbor (PPL.shiftRight ring root k) := by
  apply Fin.ext
  simp only [PPL.shiftRight, DirectedRing.rightNeighbor]
  rw [Nat.mod_add_mod]
  congr 1

private theorem referencePreparationShiftSurj {n : Nat}
    (ring : DirectedRing n) (root i : Fin n) :
    ∃ k : Nat, k < n ∧ PPL.shiftRight ring root k = i := by
  refine ⟨(i.val + n - root.val) % n, Nat.mod_lt _ ring.hn, ?_⟩
  apply Fin.ext
  simp only [PPL.shiftRight]
  rw [Nat.add_mod_mod]
  have hsum : root.val + (i.val + n - root.val) =
      i.val + n := by
    have := root.isLt
    omega
  rw [hsum, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt i.isLt

private theorem referencePreparationRightInjective {n : Nat}
    (ring : DirectedRing n) :
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

/-- Sites 0,...,j in the coordinate system rooted at the fixed
leader. This remains a meaningful closed set even after wraparound,
although the sweep uses only j<n. -/
def ReferencePreparationClockwisePrefix {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (j : Nat) (i : Fin n) : Prop :=
  ∃ k : Nat, k ≤ j ∧ i = PPL.shiftRight ring root k

theorem referencePreparationClockwisePrefixRoot {n : Nat}
    (ring : DirectedRing n) (root : Fin n) (j : Nat) :
    ReferencePreparationClockwisePrefix ring root j root := by
  refine ⟨0, Nat.zero_le j, ?_⟩
  exact (referencePreparationShiftZero ring root).symm

theorem referencePreparationClockwisePrefixZero {n : Nat}
    (ring : DirectedRing n) (root i : Fin n)
    (h : ReferencePreparationClockwisePrefix ring root 0 i) :
    i = root := by
  rcases h with ⟨k, hk, hi⟩
  have hkzero : k = 0 := by omega
  calc
    i = PPL.shiftRight ring root k := hi
    _ = PPL.shiftRight ring root 0 := by rw [hkzero]
    _ = root := referencePreparationShiftZero ring root

/-- The only incoming edge from outside a clockwise prefix has
its responder at the root. No native or probabilistic hypothesis is
needed for this directed-ring geometry. -/
theorem referencePreparationClockwisePrefixBoundary {n : Nat}
    (ring : DirectedRing n) (root : Fin n) (j : Nat) :
    ∀ i f : Fin n,
      ReferencePreparationClockwisePrefix ring root j i →
      ring.rightNeighbor f = i →
      ReferencePreparationClockwisePrefix ring root j f ∨ i = root := by
  intro i f hi hfi
  rcases hi with ⟨k, hkj, hsite⟩
  by_cases hkzero : k = 0
  · right
    calc
      i = PPL.shiftRight ring root k := hsite
      _ = PPL.shiftRight ring root 0 := by rw [hkzero]
      _ = root := referencePreparationShiftZero ring root
  · left
    have hindex : (k - 1) + 1 = k := by omega
    have hneighbor :
        ring.rightNeighbor f =
          ring.rightNeighbor (PPL.shiftRight ring root (k - 1)) := by
      calc
        ring.rightNeighbor f = i := hfi
        _ = PPL.shiftRight ring root k := hsite
        _ = PPL.shiftRight ring root ((k - 1) + 1) := by rw [hindex]
        _ = ring.rightNeighbor
              (PPL.shiftRight ring root (k - 1)) :=
            referencePreparationShiftSucc ring root (k - 1)
    have hsource : f = PPL.shiftRight ring root (k - 1) :=
      referencePreparationRightInjective ring hneighbor
    exact ⟨k - 1, by omega, hsource⟩

theorem referencePreparationClockwisePrefixCover {n : Nat}
    (ring : DirectedRing n) (root i : Fin n) :
    ReferencePreparationClockwisePrefix ring root (n - 1) i := by
  obtain ⟨k, hk, hsite⟩ :=
    referencePreparationShiftSurj ring root i
  exact ⟨k, by omega, hsite.symm⟩

/-- All arbitrary intervening nativeE edges preserve a previously
cleared clockwise prefix, provided the root is still a leader. -/
theorem referencePreparationClockwisePrefixStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n) (mask : Fin n → Bool)
    (j : Nat) (e : Fin n)
    (hroot : (N root).l = true)
    (hclear : ∀ i, ReferencePreparationClockwisePrefix
      ring root j i → mask i = false) :
    ∀ i, ReferencePreparationClockwisePrefix ring root j i →
      referencePreparationOldLabelStep ring N mask e i = false := by
  exact referencePreparationOldLabelsClosedStep
    ring root N mask e
    (ReferencePreparationClockwisePrefix ring root j)
    hroot
    (referencePreparationClockwisePrefixBoundary ring root j)
    hclear

/-- e_0 clears site zero even if the original leader hosted a
native bullet immediately before that service. -/
theorem referencePreparationClockwiseFirstService {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n) (mask : Fin n → Bool) :
    ∀ i, ReferencePreparationClockwisePrefix ring root 0 i →
      referencePreparationOldLabelStep ring N mask root i = false := by
  intro i hi
  have hsite := referencePreparationClockwisePrefixZero ring root i hi
  rw [hsite]
  exact referencePreparationOldLabelSource ring N mask root

/-- If 0,...,j is already cleared, the named e_(j+1) service
clears j+1 as well. The previous prefix is protected even on this
edge; no special case for its wraparound responder is required. -/
theorem referencePreparationClockwiseNextService {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n) (mask : Fin n → Bool)
    (j : Nat) (hroot : (N root).l = true)
    (hclear : ∀ i, ReferencePreparationClockwisePrefix
      ring root j i → mask i = false) :
    ∀ i, ReferencePreparationClockwisePrefix ring root (j + 1) i →
      referencePreparationOldLabelStep ring N mask
        (PPL.shiftRight ring root (j + 1)) i = false := by
  have hstay := referencePreparationClockwisePrefixStep
    ring root N mask j
    (PPL.shiftRight ring root (j + 1)) hroot hclear
  intro i hi
  rcases hi with ⟨k, hk, hsite⟩
  by_cases hkj : k ≤ j
  · exact hstay i ⟨k, hkj, hsite⟩
  · have heq : k = j + 1 := by omega
    have hnew : i = PPL.shiftRight ring root (j + 1) := by
      rw [heq] at hsite
      exact hsite
    rw [hnew]
    exact referencePreparationOldLabelSource ring N mask
      (PPL.shiftRight ring root (j + 1))

/-- A form of the closed-prefix invariant convenient for an
incrementing ghost cursor: every site whose offset is strictly
less than c is free of labels. -/
def ReferencePreparationBelowMask {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (mask : Fin n → Bool) (c : Nat) : Prop :=
  ∀ k : Nat, k < c →
    mask (PPL.shiftRight ring root k) = false

private theorem referencePreparationBelowBoundary {n : Nat}
    (ring : DirectedRing n) (root : Fin n) (c : Nat) :
    ∀ i f : Fin n,
      (∃ k : Nat, k < c ∧ i = PPL.shiftRight ring root k) →
      ring.rightNeighbor f = i →
      (∃ k : Nat, k < c ∧ f = PPL.shiftRight ring root k) ∨
        i = root := by
  intro i f hi hf
  by_cases hc : c = 0
  · rcases hi with ⟨k, hk, _⟩
    omega
  · have hprefix :
        ReferencePreparationClockwisePrefix ring root (c - 1) i := by
      rcases hi with ⟨k, hk, hsite⟩
      exact ⟨k, by omega, hsite⟩
    rcases referencePreparationClockwisePrefixBoundary
        ring root (c - 1) i f hprefix hf with hfrom | hroot
    · rcases hfrom with ⟨k, hk, hsite⟩
      exact Or.inl ⟨k, by omega, hsite⟩
    · exact Or.inr hroot

/-- A cursor's already-retired part stays retired on every real
nativeE edge, even when the edge is not the current nominated one. -/
theorem referencePreparationBelowPreserved {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n) (mask : Fin n → Bool)
    (c : Nat) (e : Fin n)
    (hroot : (N root).l = true)
    (hbelow : ReferencePreparationBelowMask ring root mask c) :
    ReferencePreparationBelowMask ring root
      (referencePreparationOldLabelStep ring N mask e) c := by
  have hclosed := referencePreparationOldLabelsClosedStep
    ring root N mask e
    (fun i => ∃ k : Nat, k < c ∧
      i = PPL.shiftRight ring root k)
    hroot (referencePreparationBelowBoundary ring root c)
    (by
      intro i hi
      rcases hi with ⟨k, hk, hsite⟩
      rw [hsite]
      exact hbelow k hk)
  intro k hk
  exact hclosed (PPL.shiftRight ring root k) ⟨k, hk, rfl⟩

/-- Native state, old-label mask, next expected clockwise offset.
The schedule always selects a true edge e; it never consults or
changes the extra fields. The cursor is absorbing after n hits. -/
abbrev ReferencePreparationOldCursorState (n : Nat) :=
  TripleNativeState n × ((Fin n → Bool) × Nat)

noncomputable def referencePreparationOldCursorStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ReferencePreparationOldCursorState n) (e : Fin n) :
    ReferencePreparationOldCursorState n :=
  (nativeE ring z.1 e,
    (referencePreparationOldLabelStep ring z.1 z.2.1 e,
      if z.2.2 < n then
        if e = PPL.shiftRight ring root z.2.2 then
          z.2.2 + 1 else z.2.2
      else z.2.2))

def referencePreparationOldCursorDone {n : Nat}
    (z : ReferencePreparationOldCursorState n) : Prop :=
  n ≤ z.2.2

def referencePreparationOldCursorLabelFree {n : Nat}
    (z : ReferencePreparationOldCursorState n) : Prop :=
  ∀ i : Fin n, z.2.1 i = false

def ReferencePreparationOldCursorGood {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ReferencePreparationOldCursorState n) : Prop :=
  (z.1 root).l = true ∧
  (∀ i : Fin n, (z.1 i).l = true → i = root) ∧
  PPlus ring z.1 ∧
  ReferencePreparationBelowMask ring root z.2.1 z.2.2

/-- The native component is exactly nativeE, with no birth,
candidate, or scheduler-identity approximation. -/
theorem referencePreparationOldCursorNativeStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ReferencePreparationOldCursorState n) (e : Fin n) :
    (referencePreparationOldCursorStep ring root z e).1 =
      nativeE ring z.1 e := by
  rfl

theorem referencePreparationOldCursorNativeRun {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (w : List (Fin n))
      (z : ReferencePreparationOldCursorState n),
      (LDSinkBoundedKernel.run
        (referencePreparationOldCursorStep ring root) z w).1 =
      nativeLiftNativeRun ring z.1 w := by
  intro w
  induction w with
  | nil =>
      intro z
      rfl
  | cons e es ih =>
      intro z
      change (LDSinkBoundedKernel.run
        (referencePreparationOldCursorStep ring root)
        (referencePreparationOldCursorStep ring root z e) es).1 =
        nativeLiftNativeRun ring (nativeE ring z.1 e) es
      exact ih (referencePreparationOldCursorStep ring root z e)

/-- This is the same physical projection identity used by the
earlier named-list clock, now with the ancestry history attached. -/
theorem referencePreparationOldCursorPhysicalCostEq {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (P : TripleNativeState n → Prop)
    (z : ReferencePreparationOldCursorState n) (T : Nat) :
    costNumerator (referencePreparationOldCursorStep ring root)
      (fun x => P x.1) z T =
    costNumerator (nativeE ring) P z.1 T := by
  exact Prob.costNumerator_ghost_eq
    (nativeE ring) (referencePreparationOldCursorStep ring root)
    (by intro x e; rfl) P z T

/-- In one genuine nativeE interaction, a service of the nominated
e_c clears one more site, and every other service preserves the
already-cleared part. -/
theorem referencePreparationOldCursorBelowStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n) (mask : Fin n → Bool)
    (c : Nat) (e : Fin n)
    (hroot : (N root).l = true)
    (hbelow : ReferencePreparationBelowMask ring root mask c) :
    ReferencePreparationBelowMask ring root
      (referencePreparationOldCursorStep
        ring root (N, (mask, c)) e).2.1
      (referencePreparationOldCursorStep
        ring root (N, (mask, c)) e).2.2 := by
  change ReferencePreparationBelowMask ring root
    (referencePreparationOldLabelStep ring N mask e)
    (if c < n then
      if e = PPL.shiftRight ring root c then c + 1 else c
      else c)
  have hstay := referencePreparationBelowPreserved
    ring root N mask c e hroot hbelow
  by_cases hc : c < n
  · by_cases he : e = PPL.shiftRight ring root c
    · have hadvance : ReferencePreparationBelowMask ring root
          (referencePreparationOldLabelStep ring N mask e)
          (c + 1) := by
        intro k hk
        by_cases hkc : k < c
        · exact hstay k hkc
        · have hkeq : k = c := by omega
          rw [hkeq, ← he]
          exact referencePreparationOldLabelSource ring N mask e
      simpa only [if_pos hc, if_pos he] using hadvance
    · simpa only [if_pos hc, if_neg he] using hstay
  · simpa only [if_neg hc] using hstay

theorem referencePreparationOldCursorGoodStep {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n) (root : Fin n)
    (z : ReferencePreparationOldCursorState n) (e : Fin n)
    (hgood : ReferencePreparationOldCursorGood ring root z) :
    ReferencePreparationOldCursorGood ring root
      (referencePreparationOldCursorStep ring root z e) := by
  rcases z with ⟨N, ⟨mask, c⟩⟩
  rcases hgood with ⟨hroot, hunique, hplus, hbelow⟩
  have hfixed := CandidateNativeProof.leader_fixed
    (by omega : 3 ≤ n) ring N e root hroot hunique hplus
  have hplusNext := nativeE_preserves_PPlus
    (by omega : 3 ≤ n) ring N e hplus
  exact ⟨hfixed.1, hfixed.2.1, hplusNext,
    referencePreparationOldCursorBelowStep
      ring root N mask c e hroot hbelow⟩

/-- When the cursor reaches n, surjectivity of clockwise offsets
turns the closed-prefix certificate into extinction of all initial
labels, at the ACTUAL native state of that scheduler history. -/
theorem referencePreparationOldCursorDoneNoOld {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ReferencePreparationOldCursorState n)
    (hgood : ReferencePreparationOldCursorGood ring root z)
    (hdone : referencePreparationOldCursorDone z) :
    referencePreparationOldCursorLabelFree z := by
  intro i
  obtain ⟨k, hk, hsite⟩ :=
    referencePreparationShiftSurj ring root i
  have hbelow : ReferencePreparationBelowMask ring root
      z.2.1 z.2.2 := hgood.2.2.2
  have hmask : z.2.1 (PPL.shiftRight ring root k) = false :=
    hbelow k (by
      change n ≤ z.2.2 at hdone
      omega)
  rw [hsite] at hmask
  exact hmask

/-- One nominated scheduler edge increases the cursor by one.
This is a real selected edge, not a request to execute an entire
word atomically. -/
theorem referencePreparationOldCursorDrop {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ReferencePreparationOldCursorState n)
    (h : ¬ referencePreparationOldCursorDone z) :
    n - (referencePreparationOldCursorStep ring root z
      (PPL.shiftRight ring root z.2.2)).2.2 + 1 ≤
        n - z.2.2 := by
  have hc : z.2.2 < n := by
    change ¬ n ≤ z.2.2 at h
    omega
  simp only [referencePreparationOldCursorStep,
    if_pos hc, if_pos rfl, ↓reduceIte]
  omega

/-- Every other scheduler edge leaves the cursor alone or advances
it, so the remaining quota n-c never increases. -/
theorem referencePreparationOldCursorNonincrease {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ReferencePreparationOldCursorState n)
    (_h : ¬ referencePreparationOldCursorDone z) (e : Fin n) :
    n - (referencePreparationOldCursorStep ring root z e).2.2 ≤
      n - z.2.2 := by
  by_cases hc : z.2.2 < n
  · by_cases he : e = PPL.shiftRight ring root z.2.2
    · simp only [referencePreparationOldCursorStep,
        if_pos hc, if_pos he, ↓reduceIte]
      omega
    · simp only [referencePreparationOldCursorStep,
        if_pos hc, if_neg he, ↓reduceIte]
      omega
  · simp only [referencePreparationOldCursorStep,
      if_neg hc, ↓reduceIte]
    omega

/-- Scheduler-clock cost, n times n expected interactions. It is
the cursor counterpart of referencePreparationForwardClockCost
and keeps all intervening nativeE services. -/
theorem referencePreparationOldCursorClockCost {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ReferencePreparationOldCursorState n) (T : Nat) :
    costNumerator (referencePreparationOldCursorStep ring root)
      referencePreparationOldCursorDone z T ≤
      n ^ T * (n * (n - z.2.2)) := by
  exact Prob.costNumerator_le_of_nominated_edge
    (referencePreparationOldCursorStep ring root)
    referencePreparationOldCursorDone
    (fun x : ReferencePreparationOldCursorState n => n - x.2.2)
    (fun x : ReferencePreparationOldCursorState n =>
      PPL.shiftRight ring root x.2.2)
    (referencePreparationOldCursorDrop ring root)
    (referencePreparationOldCursorNonincrease ring root)
    z T

/-- Under the invariant, early extinction can only be cheaper than
waiting for the full ordered sweep. This proof is horizon-by-horizon
and uses the same actual nativeE child at every edge. -/
theorem referencePreparationOldCursorLabelCostLeClock {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n) (root : Fin n) :
    ∀ (T : Nat) (z : ReferencePreparationOldCursorState n),
      ReferencePreparationOldCursorGood ring root z →
      costNumerator (referencePreparationOldCursorStep ring root)
        referencePreparationOldCursorLabelFree z T ≤
      costNumerator (referencePreparationOldCursorStep ring root)
        referencePreparationOldCursorDone z T := by
  intro T
  induction T with
  | zero =>
      intro z _
      simp only [costNumerator_zero]
      exact Nat.le_refl 0
  | succ T ih =>
      intro z hgood
      by_cases hfree : referencePreparationOldCursorLabelFree z
      · rw [costNumerator_terminal
          (referencePreparationOldCursorStep ring root)
          referencePreparationOldCursorLabelFree z hfree (T + 1)]
        exact Nat.zero_le _
      · have hnotdone : ¬ referencePreparationOldCursorDone z := by
          intro hdone
          exact hfree (referencePreparationOldCursorDoneNoOld
            ring root z hgood hdone)
        rw [costNumerator_succ
            (referencePreparationOldCursorStep ring root)
            referencePreparationOldCursorLabelFree z hfree T,
          costNumerator_succ
            (referencePreparationOldCursorStep ring root)
            referencePreparationOldCursorDone z hnotdone T]
        have hs := ofFn_sum_le
          (fun e : Fin n =>
            costNumerator (referencePreparationOldCursorStep ring root)
              referencePreparationOldCursorLabelFree
              (referencePreparationOldCursorStep ring root z e) T)
          (fun e : Fin n =>
            costNumerator (referencePreparationOldCursorStep ring root)
              referencePreparationOldCursorDone
              (referencePreparationOldCursorStep ring root z e) T)
          (fun e => ih (referencePreparationOldCursorStep ring root z e)
            (referencePreparationOldCursorGoodStep hn ring root z e hgood))
        exact Nat.add_le_add_left hs _

/-- FINISHED FIRST CUT (H.2), at the actual birth-free nativeE
trajectory with an analytical ancestry marker. Both live and dummy
bullets at the singleton cut can be labeled. No post-cut firing
acquires a label. The cut is adapted to the scheduler history. -/
theorem referencePreparationOldLabelsFirstCost {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n)
    (hroot : (N root).l = true)
    (hunique : ∀ i : Fin n, (N i).l = true → i = root)
    (hplus : PPlus ring N) (mask : Fin n → Bool) (T : Nat) :
    costNumerator (referencePreparationOldCursorStep ring root)
      referencePreparationOldCursorLabelFree
      (N, (mask, 0)) T ≤ n ^ T * n ^ 2 := by
  have hgood : ReferencePreparationOldCursorGood ring root
      (N, (mask, 0)) := by
    refine ⟨hroot, hunique, hplus, ?_⟩
    intro k hk
    exact absurd hk (Nat.not_lt_zero k)
  have hcompare := referencePreparationOldCursorLabelCostLeClock
    hn ring root T (N, (mask, 0)) hgood
  have hclock := referencePreparationOldCursorClockCost
    ring root (N, (mask, 0)) T
  have h := Nat.le_trans hcompare hclock
  simpa only [Nat.sub_zero, Nat.pow_two] using h

/-- Specialization to the literal initial inheritance marks at the
singleton cut. This is the paper's old-bullet-retirement event, not
a claim that the physical native state contains no NEW bullet. -/
theorem referencePreparationInitialOldLabelsFirstCost {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n)
    (hroot : (N root).l = true)
    (hunique : ∀ i : Fin n, (N i).l = true → i = root)
    (hplus : PPlus ring N) (T : Nat) :
    costNumerator (referencePreparationOldCursorStep ring root)
      referencePreparationOldCursorLabelFree
      (N, (referencePreparationInitialOldLabels N, 0)) T ≤
        n ^ T * n ^ 2 := by
  exact referencePreparationOldLabelsFirstCost hn ring root N
    hroot hunique hplus (referencePreparationInitialOldLabels N) T

/-- Ghost-lifted six-stage first-cut consumer. It is the exact
counterpart of referencePreparationSixStageCostOfCuts, with the
first stopping predicate historical and the last predicate physical.
The OTHER FIVE native/candidate stage bounds are explicit premises.
The final cost is projected back to nativeE, not merely asserted
for a ghost process. -/
theorem referencePreparationSixStageCostWithOldFirst {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n)
    (hroot : (N root).l = true)
    (hunique : ∀ i : Fin n, (N i).l = true → i = root)
    (hplus : PPlus ring N)
    (mask : Fin n → Bool)
    (B C D E : ReferencePreparationOldCursorState n → Prop)
    (P : TripleNativeState n → Prop)
    (hsecond : ∀ z, referencePreparationOldCursorLabelFree z →
      ∀ T, costNumerator (referencePreparationOldCursorStep ring root)
        (fun x => B x ∨ P x.1) z T ≤ n ^ T * n ^ 2)
    (hthird : ∀ z, B z →
      ∀ T, costNumerator (referencePreparationOldCursorStep ring root)
        (fun x => C x ∨ P x.1) z T ≤ n ^ T * n ^ 2)
    (hfourth : ∀ z, C z →
      ∀ T, costNumerator (referencePreparationOldCursorStep ring root)
        (fun x => D x ∨ P x.1) z T ≤ n ^ T * n ^ 2)
    (hfifth : ∀ z, D z →
      ∀ T, costNumerator (referencePreparationOldCursorStep ring root)
        (fun x => E x ∨ P x.1) z T ≤ n ^ T * n ^ 2)
    (hsixth : ∀ z, E z →
      ∀ T, costNumerator (referencePreparationOldCursorStep ring root)
        (fun x => P x.1) z T ≤ n ^ T * n ^ 2) :
    ∀ T, costNumerator (nativeE ring) P N T ≤
      n ^ T * (6 * n ^ 2) := by
  have hfirst : ∀ T,
      costNumerator (referencePreparationOldCursorStep ring root)
        (fun z => referencePreparationOldCursorLabelFree z ∨ P z.1)
        (N, (mask, 0)) T ≤ n ^ T * n ^ 2 := by
    intro T
    have hmono := Prob.costNumerator_target_mono
      (referencePreparationOldCursorStep ring root)
      referencePreparationOldCursorLabelFree
      (fun z => referencePreparationOldCursorLabelFree z ∨ P z.1)
      (by intro z hz; exact Or.inl hz)
      (N, (mask, 0)) T
    exact Nat.le_trans hmono
      (referencePreparationOldLabelsFirstCost
        hn ring root N hroot hunique hplus mask T)
  have hD : ∀ z, D z → ∀ T,
      costNumerator (referencePreparationOldCursorStep ring root)
        (fun x => P x.1) z T ≤ n ^ T * (2 * n ^ 2) := by
    intro z hz T
    have h := Prob.costNumerator_stage_le
      (referencePreparationOldCursorStep ring root)
      z E (fun x => P x.1) (n ^ 2) (n ^ 2)
      (hfifth z hz) hsixth T
    have heq : n ^ 2 + n ^ 2 = 2 * n ^ 2 := by omega
    rw [heq] at h
    exact h
  have hC : ∀ z, C z → ∀ T,
      costNumerator (referencePreparationOldCursorStep ring root)
        (fun x => P x.1) z T ≤ n ^ T * (3 * n ^ 2) := by
    intro z hz T
    have h := Prob.costNumerator_stage_le
      (referencePreparationOldCursorStep ring root)
      z D (fun x => P x.1) (n ^ 2) (2 * n ^ 2)
      (hfourth z hz) hD T
    have heq : n ^ 2 + 2 * n ^ 2 = 3 * n ^ 2 := by omega
    rw [heq] at h
    exact h
  have hB : ∀ z, B z → ∀ T,
      costNumerator (referencePreparationOldCursorStep ring root)
        (fun x => P x.1) z T ≤ n ^ T * (4 * n ^ 2) := by
    intro z hz T
    have h := Prob.costNumerator_stage_le
      (referencePreparationOldCursorStep ring root)
      z C (fun x => P x.1) (n ^ 2) (3 * n ^ 2)
      (hthird z hz) hC T
    have heq : n ^ 2 + 3 * n ^ 2 = 4 * n ^ 2 := by omega
    rw [heq] at h
    exact h
  have hA : ∀ z, referencePreparationOldCursorLabelFree z → ∀ T,
      costNumerator (referencePreparationOldCursorStep ring root)
        (fun x => P x.1) z T ≤ n ^ T * (5 * n ^ 2) := by
    intro z hz T
    have h := Prob.costNumerator_stage_le
      (referencePreparationOldCursorStep ring root)
      z B (fun x => P x.1) (n ^ 2) (4 * n ^ 2)
      (hsecond z hz) hB T
    have heq : n ^ 2 + 4 * n ^ 2 = 5 * n ^ 2 := by omega
    rw [heq] at h
    exact h
  intro T
  have h := Prob.costNumerator_stage_le
    (referencePreparationOldCursorStep ring root)
    (N, (mask, 0))
    referencePreparationOldCursorLabelFree (fun x => P x.1)
    (n ^ 2) (5 * n ^ 2)
    hfirst hA T
  have heq : n ^ 2 + 5 * n ^ 2 = 6 * n ^ 2 := by omega
  rw [heq] at h
  rw [referencePreparationOldCursorPhysicalCostEq ring root
    P (N, (mask, 0)) T] at h
  exact h

end L3

/-!
Generated ancestry, zero trails, and the second physical cut.
No changes above this line.
The ancestry theorem starts with the literal initial old-label mask.
An arbitrary all-false mask is not treated as generated provenance.
The drain clock reuses the cursor, initialized at the current
bullet's offset. All non-nominated nativeE services remain active.
-/

namespace L3
namespace ReferencePreparationTrail

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

private theorem threeCases (b : Fin 3) :
    b = (0 : Fin 3) ∨ b = (1 : Fin 3) ∨ b = (2 : Fin 3) := by
  rcases b with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · omega

/-- Small literal-pair certificates; no replacement transition. -/
private structure RowFacts (x y : CertNative) : Prop where
  source_empty : (certLiteralEPair x y).1.b = (0 : Fin 3)
  responder_zero : y.sg = false → (certLiteralEPair x y).2.sg = false
  interior_zero : x.sg = false → y.sg = false → y.l = false →
    (certLiteralEPair x y).1.sg = false
  front_zero : x.sg = false → x.b ≠ (0 : Fin 3) → y.l = false →
    (certLiteralEPair x y).1.sg = false ∧
    (certLiteralEPair x y).2.sg = false
  nofire_bullet : ¬ (x.l = true ∧ x.sg = true) →
    ¬ (y.l = true ∧ y.sg = true) →
    (certLiteralEPair x y).2.b =
      (if y.l = true then y.b else if y.b = (0 : Fin 3) then x.b else y.b)
  fresh_out_zero : x.l = true → x.sg = true → y.l = false →
    (certLiteralEPair x y).1.sg = false ∧
    (certLiteralEPair x y).2.sg = false
  leader_zero : y.l = true → (certLiteralEPair x y).2.sg = false

/-- The 24 native certificate cells. -/
private def allCertNative : List CertNative :=
  [false, true].flatMap fun l => [(0 : Fin 3), 1, 2].flatMap fun b =>
    [false, true].flatMap fun sh => [false, true].map fun sg =>
      ({ l := l, b := b, sh := sh, sg := sg } : CertNative)

private theorem mem_allCertNative (x : CertNative) : x ∈ allCertNative := by
  rcases x with ⟨l, b, sh, sg⟩
  rcases threeCases b with rfl | rfl | rfl <;> cases l <;> cases sh <;> cases sg <;> decide

/-- `RowFacts` as a Boolean. -/
private def rowFactsB (x y : CertNative) : Bool :=
  decide ((certLiteralEPair x y).1.b = (0 : Fin 3)) &&
    decide (y.sg = false → (certLiteralEPair x y).2.sg = false) &&
    decide (x.sg = false → y.sg = false → y.l = false → (certLiteralEPair x y).1.sg = false) &&
    decide (x.sg = false → x.b ≠ (0 : Fin 3) → y.l = false → (certLiteralEPair x y).1.sg = false ∧ (certLiteralEPair x y).2.sg = false) &&
    decide (¬ (x.l = true ∧ x.sg = true) → ¬ (y.l = true ∧ y.sg = true) → (certLiteralEPair x y).2.b = (if y.l = true then y.b else if y.b = (0 : Fin 3) then x.b else y.b)) &&
    decide (x.l = true → x.sg = true → y.l = false → (certLiteralEPair x y).1.sg = false ∧ (certLiteralEPair x y).2.sg = false) &&
    decide (y.l = true → (certLiteralEPair x y).2.sg = false)

/-- `RowFacts` on every pair of cells: one closed evaluation (576 pairs). -/
private theorem rowFactsB_all :
    allCertNative.all (fun x => allCertNative.all fun y => rowFactsB x y) = true := by
  decide +kernel

private theorem literalFacts (x y : CertNative) : RowFacts x y := by
  have h := List.all_eq_true.mp
    (List.all_eq_true.mp rowFactsB_all x (mem_allCertNative x)) y (mem_allCertNative y)
  simp only [rowFactsB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

private theorem rightNe {n : Nat} (hn : 5 ≤ n)
    (ring : DirectedRing n) (e : Fin n) : ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  by_cases hlt : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega

private theorem shiftFull {n : Nat} (ring : DirectedRing n) (root : Fin n) :
    PPL.shiftRight ring root n = root := by
  apply Fin.ext
  change (root.val + n) % n = root.val
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt root.isLt]

private theorem shiftInjective {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (a b : Nat) (ha : a < n) (hb : b < n)
    (he : PPL.shiftRight ring root a = PPL.shiftRight ring root b) : a = b := by
  have hpos (k : Nat) (hk : k < n) :
      PPL.cyclicOffset ring root (PPL.shiftRight ring root k) = k := by
    change (((root.val + k) % n + n - root.val) % n) = k
    by_cases hs : root.val + k < n
    · rw [Nat.mod_eq_of_lt hs]
      have hh : root.val + k + n - root.val = n + k := by omega
      rw [hh, Nat.add_mod_left, Nat.mod_eq_of_lt hk]
    · have hge : n ≤ root.val + k := by omega
      have hlt : root.val + k - n < n := by omega
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
      have hh : root.val + k - n + n - root.val = k := by omega
      rw [hh, Nat.mod_eq_of_lt hk]
  have hv := congrArg (PPL.cyclicOffset ring root) he
  rw [hpos a ha, hpos b hb] at hv
  exact hv

private theorem frame {n : Nat} (ring : DirectedRing n)
    (N : TripleNativeState n) (e i : Fin n)
    (he : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    nativeE ring N e i = N i := by
  simp only [nativeE, if_neg he, if_neg hj]

private theorem follower {n : Nat} (N : TripleNativeState n) (root i : Fin n)
    (hu : ∀ j : Fin n, (N j).l = true → j = root) (hne : i ≠ root) :
    (N i).l = false := by
  cases hl : (N i).l with
  | false => rfl
  | true => exact False.elim (hne (hu i hl))

/-- Inclusive zero trail, in clockwise coordinates from the fixed root. -/
def ZeroTrail {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n) (p : Nat) : Prop :=
  ∀ k : Nat, k ≤ p → (N (PPL.shiftRight ring root k)).sg = false

theorem trailRootZero {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n) (p : Nat) (h : ZeroTrail ring root N p) :
    (N root).sg = false := by
  have hz := h 0 (Nat.zero_le p)
  rw [referencePreparationShiftZero] at hz
  exact hz

private theorem noFire {n : Nat} (N : TripleNativeState n) (root : Fin n)
    (hu : ∀ i : Fin n, (N i).l = true → i = root)
    (hz : (N root).sg = false) (i : Fin n) :
    ¬ ((N i).l = true ∧ (N i).sg = true) := by
  intro h
  have hi := hu i h.1
  have hs := h.2
  rw [hi, hz] at hs
  cases hs

/-- Every non-host service preserves the entire zero prefix.
This allows arbitrary bullets, labels, shields and signals outside it. -/
theorem trailStay {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n) (p : Nat) (e : Fin n)
    (hp : p < n)
    (hu : ∀ i : Fin n, (N i).l = true → i = root)
    (ht : ZeroTrail ring root N p)
    (hne : PPL.shiftRight ring root p ≠ e) :
    ZeroTrail ring root (nativeE ring N e) p := by
  have hpair := sealed_prep_actual_old_pair ring N e (rightNe hn ring e)
  intro k hk
  by_cases hsrc : PPL.shiftRight ring root k = e
  · have hkp : k < p := by
      by_cases heq : k = p
      · rw [heq] at hsrc
        exact False.elim (hne hsrc)
      · omega
    have hj : ring.rightNeighbor e = PPL.shiftRight ring root (k + 1) := by
      rw [← hsrc, ← referencePreparationShiftSucc]
    have hyl : (N (ring.rightNeighbor e)).l = false := by
      apply follower N root (ring.rightNeighbor e) hu
      rw [hj]
      exact referencePreparation_sealed_site_ne ring root (k + 1)
        (by omega) (by omega)
    have hxs := ht k hk
    rw [hsrc] at hxs
    have hys := ht (k + 1) (by omega)
    rw [← hj] at hys
    rw [hsrc, hpair.1]
    exact (literalFacts (N e) (N (ring.rightNeighbor e))).interior_zero hxs hys hyl
  · by_cases hdst : PPL.shiftRight ring root k = ring.rightNeighbor e
    · have hys := ht k hk
      rw [hdst] at hys
      rw [hdst, hpair.2]
      exact (literalFacts (N e) (N (ring.rightNeighbor e))).responder_zero hys
    · rw [frame ring N e (PPL.shiftRight ring root k) hsrc hdst]
      exact ht k hk

/-- A non-wrapping outgoing service of a bullet extends its zero
trail. This remains true even if the incoming bullet loses a collision. -/
theorem trailAdvance {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n) (p : Nat)
    (hp : p + 1 < n)
    (hu : ∀ i : Fin n, (N i).l = true → i = root)
    (hb : (N (PPL.shiftRight ring root p)).b ≠ (0 : Fin 3))
    (ht : ZeroTrail ring root N p) :
    ZeroTrail ring root (nativeE ring N (PPL.shiftRight ring root p)) (p + 1) := by
  have hj : ring.rightNeighbor (PPL.shiftRight ring root p) =
      PPL.shiftRight ring root (p + 1) :=
    (referencePreparationShiftSucc ring root p).symm
  have hyl : (N (ring.rightNeighbor (PPL.shiftRight ring root p))).l = false := by
    apply follower N root _ hu
    rw [hj]
    exact referencePreparation_sealed_site_ne ring root (p + 1) (by omega) hp
  have hrow := (literalFacts (N (PPL.shiftRight ring root p))
    (N (ring.rightNeighbor (PPL.shiftRight ring root p)))).front_zero
    (ht p (Nat.le_refl p)) hb hyl
  have hpair := sealed_prep_actual_old_pair ring N (PPL.shiftRight ring root p)
    (rightNe hn ring (PPL.shiftRight ring root p))
  intro k hk
  by_cases hlast : k = p + 1
  · rw [hlast, ← hj, hpair.2]
    exact hrow.2
  · by_cases hfront : k = p
    · rw [hfront, hpair.1]
      exact hrow.1
    · have hkp : k < p := by omega
      have hne : PPL.shiftRight ring root k ≠ PPL.shiftRight ring root p := by
        intro he
        have hh := shiftInjective ring root k p (by omega) (by omega) he
        omega
      have hshort : ZeroTrail ring root N k := by
        intro q hq
        exact ht q (by omega)
      exact trailStay hn ring root N k (PPL.shiftRight ring root p)
        (by omega) hu hshort hne k (Nat.le_refl k)

/-- Unlabelled and occupied, not merely a false Boolean on an empty site. -/
def GeneratedAt {n : Nat} (N : TripleNativeState n)
    (mask : Fin n → Bool) (i : Fin n) : Prop :=
  (N i).b ≠ (0 : Fin 3) ∧ mask i = false

def GeneratedTrails {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n) (mask : Fin n → Bool) : Prop :=
  ∀ i : Fin n, GeneratedAt N mask i →
    ∃ p : Nat, p < n ∧ i = PPL.shiftRight ring root p ∧ ZeroTrail ring root N p

def GeneratedUnique {n : Nat} (N : TripleNativeState n)
    (mask : Fin n → Bool) : Prop :=
  ∀ i j : Fin n, GeneratedAt N mask i → GeneratedAt N mask j → i = j

def GeneratedInvariant {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n) (mask : Fin n → Bool) : Prop :=
  GeneratedTrails ring root N mask ∧ GeneratedUnique N mask

/-- `literalGeneratedOrigins` as a Boolean. -/
private def genOriginsB (x y : CertNative) (mx my : Bool) : Bool :=
  decide (((certLiteralEPair x y).2.b ≠ (0 : Fin 3)) →
    (¬ ((my = true ∧ ¬ (y.l = true ∧ y.sg = true)) ∨
      (mx = true ∧ x.b ≠ (0 : Fin 3) ∧ ¬ (x.l = true ∧ x.sg = true) ∧
        y.l = false ∧ y.b = (0 : Fin 3)))) →
    (y.b ≠ (0 : Fin 3) ∧ my = false) ∨
    (x.b ≠ (0 : Fin 3) ∧ mx = false ∧ y.l = false ∧ y.b = (0 : Fin 3)) ∨
    (y.l = true ∧ y.sg = true) ∨
    (x.l = true ∧ x.sg = true ∧ y.l = false ∧ y.b = (0 : Fin 3)))

/-- `literalGeneratedOrigins` on every pair of cells and marks: one closed evaluation (2304). -/
private theorem genOriginsB_all :
    allCertNative.all (fun x => allCertNative.all fun y =>
      [false, true].all fun mx => [false, true].all fun my => genOriginsB x y mx my) = true := by
  decide +kernel

private theorem literalGeneratedOrigins (x y : CertNative) (mx my : Bool)
    (hb : (certLiteralEPair x y).2.b ≠ (0 : Fin 3))
    (hm : ¬ ((my = true ∧ ¬ (y.l = true ∧ y.sg = true)) ∨
      (mx = true ∧ x.b ≠ (0 : Fin 3) ∧ ¬ (x.l = true ∧ x.sg = true) ∧
        y.l = false ∧ y.b = (0 : Fin 3)))) :
    (y.b ≠ (0 : Fin 3) ∧ my = false) ∨
    (x.b ≠ (0 : Fin 3) ∧ mx = false ∧ y.l = false ∧ y.b = (0 : Fin 3)) ∨
    (y.l = true ∧ y.sg = true) ∨
    (x.l = true ∧ x.sg = true ∧ y.l = false ∧ y.b = (0 : Fin 3)) := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp genOriginsB_all x (mem_allCertNative x)) y (mem_allCertNative y))
    mx (by cases mx <;> decide)) my (by cases my <;> decide)
  exact of_decide_eq_true h hb hm

/-- Complete old-resident, transported-source, incoming firing,
and outgoing firing alternatives for a post-step generated bullet. -/
theorem generatedCases {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (N : TripleNativeState n) (mask : Fin n → Bool) (e i : Fin n)
    (h : GeneratedAt (nativeE ring N e)
      (referencePreparationOldLabelStep ring N mask e) i) :
    (GeneratedAt N mask i ∧ i ≠ e) ∨
    (i = ring.rightNeighbor e ∧ GeneratedAt N mask e ∧
      (N (ring.rightNeighbor e)).l = false ∧ (N (ring.rightNeighbor e)).b = (0 : Fin 3)) ∨
    (i = ring.rightNeighbor e ∧ (N (ring.rightNeighbor e)).l = true ∧
      (N (ring.rightNeighbor e)).sg = true) ∨
    (i = ring.rightNeighbor e ∧ (N e).l = true ∧ (N e).sg = true ∧
      (N (ring.rightNeighbor e)).l = false ∧ (N (ring.rightNeighbor e)).b = (0 : Fin 3)) := by
  have hpair := sealed_prep_actual_old_pair ring N e (rightNe hn ring e)
  by_cases he : i = e
  · have hb := h.1
    rw [he, hpair.1, (literalFacts (N e) (N (ring.rightNeighbor e))).source_empty] at hb
    exact False.elim (hb rfl)
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      have hb : (certLiteralEPair (N e) (N (ring.rightNeighbor e))).2.b ≠ (0 : Fin 3) := by
        rw [← hpair.2]
        exact h.1
      have hm : ¬ ((mask (ring.rightNeighbor e) = true ∧
          ¬ ((N (ring.rightNeighbor e)).l = true ∧ (N (ring.rightNeighbor e)).sg = true)) ∨
        (mask e = true ∧ (N e).b ≠ (0 : Fin 3) ∧
          ¬ ((N e).l = true ∧ (N e).sg = true) ∧
          (N (ring.rightNeighbor e)).l = false ∧ (N (ring.rightNeighbor e)).b = (0 : Fin 3))) := by
        intro hh
        have hz := h.2
        rw [referencePreparationOldLabelResponder ring N mask e (rightNe hn ring e),
          if_pos ⟨h.1, hh⟩] at hz
        cases hz
      rcases literalGeneratedOrigins (N e) (N (ring.rightNeighbor e))
          (mask e) (mask (ring.rightNeighbor e)) hb hm with hr | ht | hy | hx
      · exact Or.inl ⟨hr, he⟩
      · exact Or.inr (Or.inl ⟨rfl, ⟨ht.1, ht.2.1⟩, ht.2.2.1, ht.2.2.2⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, hy.1, hy.2⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2⟩))
    · have hb := h.1
      have hm := h.2
      rw [frame ring N e i he hj] at hb
      rw [referencePreparationOldLabelFrame ring N mask e i he hj] at hm
      exact Or.inl ⟨⟨hb, hm⟩, he⟩

theorem generatedRootZero {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n) (mask : Fin n → Bool)
    (ht : GeneratedTrails ring root N mask) (i : Fin n) (hi : GeneratedAt N mask i) :
    (N root).sg = false := by
  obtain ⟨p, _, _, hp⟩ := ht i hi
  exact trailRootZero ring root N p hp

theorem generatedNoFiring {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n) (mask : Fin n → Bool)
    (hu : ∀ i : Fin n, (N i).l = true → i = root)
    (ht : GeneratedTrails ring root N mask) (i : Fin n) (hi : GeneratedAt N mask i) :
    ∀ j : Fin n, ¬ ((N j).l = true ∧ (N j).sg = true) := by
  exact noFire N root hu (generatedRootZero ring root N mask ht i hi)

/-- All-edge generated-trail preservation, including both kinds of fresh firing. -/
theorem generatedTrailsStep {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n) (mask : Fin n → Bool) (e : Fin n)
    (hr : (N root).l = true)
    (hu : ∀ i : Fin n, (N i).l = true → i = root)
    (ht : GeneratedTrails ring root N mask) :
    GeneratedTrails ring root (nativeE ring N e)
      (referencePreparationOldLabelStep ring N mask e) := by
  have hpair := sealed_prep_actual_old_pair ring N e (rightNe hn ring e)
  intro i hi
  rcases generatedCases hn ring N mask e i hi with hstay | hmove | hfresh | hout
  · obtain ⟨p, hp, hs, hz⟩ := ht i hstay.1
    refine ⟨p, hp, hs, ?_⟩
    exact trailStay hn ring root N p e hp hu hz
      (by intro he; exact hstay.2 (hs.trans he))
  · obtain ⟨p, hp, hs, hz⟩ := ht e hmove.2.1
    have hnext : p + 1 < n := by
      by_cases hnxt : p + 1 < n
      · exact hnxt
      · have hlast : p + 1 = n := by omega
        have hj : ring.rightNeighbor e = root := by
          calc
            ring.rightNeighbor e = ring.rightNeighbor (PPL.shiftRight ring root p) :=
              congrArg ring.rightNeighbor hs
            _ = PPL.shiftRight ring root (p + 1) := (referencePreparationShiftSucc ring root p).symm
            _ = PPL.shiftRight ring root n := by rw [hlast]
            _ = root := shiftFull ring root
        have hfalse := hmove.2.2.1
        rw [hj, hr] at hfalse
        cases hfalse
    have hsite : i = PPL.shiftRight ring root (p + 1) := by
      rw [hmove.1, hs, ← referencePreparationShiftSucc]
    have hb : (N (PPL.shiftRight ring root p)).b ≠ (0 : Fin 3) := by
      rw [← hs]
      exact hmove.2.1.1
    have hznext := trailAdvance hn ring root N p hnext hu hb hz
    rw [← hs] at hznext
    exact ⟨p + 1, hnext, hsite, hznext⟩
  · have hj : ring.rightNeighbor e = root := hu _ hfresh.2.1
    have hzroot : (nativeE ring N e root).sg = false := by
      rw [← hj, hpair.2]
      exact (literalFacts (N e) (N (ring.rightNeighbor e))).leader_zero hfresh.2.1
    refine ⟨0, ring.hn, ?_, ?_⟩
    · rw [referencePreparationShiftZero]
      exact hfresh.1.trans hj
    · intro k hk
      have hkzero : k = 0 := by omega
      rw [hkzero, referencePreparationShiftZero]
      exact hzroot
  · have he : e = root := hu e hout.2.1
    have hj : PPL.shiftRight ring root 1 = ring.rightNeighbor e := by
      calc
        PPL.shiftRight ring root 1 = ring.rightNeighbor (PPL.shiftRight ring root 0) :=
          referencePreparationShiftSucc ring root 0
        _ = ring.rightNeighbor root := by rw [referencePreparationShiftZero]
        _ = ring.rightNeighbor e := by rw [he]
    have hz := (literalFacts (N e) (N (ring.rightNeighbor e))).fresh_out_zero
      hout.2.1 hout.2.2.1 hout.2.2.2.1
    have hzroot : (nativeE ring N e root).sg = false := by
      rw [← he, hpair.1]
      exact hz.1
    have hznext : (nativeE ring N e (PPL.shiftRight ring root 1)).sg = false := by
      rw [hj, hpair.2]
      exact hz.2
    refine ⟨1, by omega, hout.1.trans hj.symm, ?_⟩
    intro k hk
    have hkcases : k = 0 ∨ k = 1 := by omega
    rcases hkcases with hkzero | hkone
    · rw [hkzero, referencePreparationShiftZero]
      exact hzroot
    · rw [hkone]
      exact hznext

private theorem generatedOrigin {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n) (mask : Fin n → Bool) (e i : Fin n)
    (hu : ∀ j : Fin n, (N j).l = true → j = root)
    (h : GeneratedAt (nativeE ring N e) (referencePreparationOldLabelStep ring N mask e) i) :
    (GeneratedAt N mask i ∧ i ≠ e) ∨
      (i = ring.rightNeighbor e ∧ (GeneratedAt N mask e ∨ (N root).sg = true)) := by
  rcases generatedCases hn ring N mask e i h with hr | hm | hy | hx
  · exact Or.inl hr
  · exact Or.inr ⟨hm.1, Or.inl hm.2.1⟩
  · have hs := hy.2.2
    rw [hu _ hy.2.1] at hs
    exact Or.inr ⟨hy.1, Or.inr hs⟩
  · have hs := hx.2.2.1
    rw [hu e hx.2.1] at hs
    exact Or.inr ⟨hx.1, Or.inr hs⟩

/-- Uniqueness is an induction invariant, not an inference from zero
trails alone. A fresh firing is incompatible with any old generated survivor. -/
theorem generatedUniqueStep {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n) (mask : Fin n → Bool) (e : Fin n)
    (hu : ∀ i : Fin n, (N i).l = true → i = root)
    (ht : GeneratedTrails ring root N mask) (hg : GeneratedUnique N mask) :
    GeneratedUnique (nativeE ring N e) (referencePreparationOldLabelStep ring N mask e) := by
  intro i j hi hj
  rcases generatedOrigin hn ring root N mask e i hu hi with hiold | hinew
  · rcases generatedOrigin hn ring root N mask e j hu hj with hjold | hjnew
    · exact hg i j hiold.1 hjold.1
    · rcases hjnew.2 with hsource | hready
      · exact False.elim (hiold.2 (hg i e hiold.1 hsource))
      · have hz := generatedRootZero ring root N mask ht i hiold.1
        rw [hz] at hready
        cases hready
  · rcases generatedOrigin hn ring root N mask e j hu hj with hjold | hjnew
    · rcases hinew.2 with hsource | hready
      · exact False.elim (hjold.2 (hg j e hjold.1 hsource))
      · have hz := generatedRootZero ring root N mask ht j hjold.1
        rw [hz] at hready
        cases hready
    · exact hinew.1.trans hjnew.1.symm

theorem generatedInvariantStep {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n) (mask : Fin n → Bool) (e : Fin n)
    (hr : (N root).l = true)
    (hu : ∀ i : Fin n, (N i).l = true → i = root)
    (h : GeneratedInvariant ring root N mask) :
    GeneratedInvariant ring root (nativeE ring N e)
      (referencePreparationOldLabelStep ring N mask e) := by
  exact ⟨generatedTrailsStep hn ring root N mask e hr hu h.1,
    generatedUniqueStep hn ring root N mask e hu h.1 h.2⟩

theorem initialGeneratedInvariant {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n) :
    GeneratedInvariant ring root N (referencePreparationInitialOldLabels N) := by
  have hnone : ∀ i : Fin n, ¬ GeneratedAt N (referencePreparationInitialOldLabels N) i := by
    intro i hi
    have hm := hi.2
    rw [referencePreparationInitialOldLabels, if_neg hi.1] at hm
    cases hm
  constructor
  · intro i hi
    exact False.elim (hnone i hi)
  · intro i j hi hj
    exact False.elim (hnone i hi)

def GeneratedGood {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (z : ReferencePreparationOldCursorState n) : Prop :=
  (z.1 root).l = true ∧
  (∀ i : Fin n, (z.1 i).l = true → i = root) ∧
  PPlus ring z.1 ∧ GeneratedInvariant ring root z.1 z.2.1

theorem generatedGoodStep {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (z : ReferencePreparationOldCursorState n) (e : Fin n)
    (h : GeneratedGood ring root z) :
    GeneratedGood ring root (referencePreparationOldCursorStep ring root z e) := by
  have hf := CandidateNativeProof.leader_fixed (by omega : 3 ≤ n)
    ring z.1 e root h.1 h.2.1 h.2.2.1
  exact ⟨hf.1, hf.2.1,
    nativeE_preserves_PPlus (by omega : 3 ≤ n) ring z.1 e h.2.2.1,
    generatedInvariantStep hn ring root z.1 z.2.1 e h.1 h.2.1 h.2.2.2⟩

theorem generatedGoodRun {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) : ∀ (w : List (Fin n)) (z : ReferencePreparationOldCursorState n),
    GeneratedGood ring root z → GeneratedGood ring root
      (LDSinkBoundedKernel.run (referencePreparationOldCursorStep ring root) z w) := by
  intro w
  induction w with
  | nil =>
      intro z hz
      exact hz
  | cons e es ih =>
      intro z hz
      exact ih (referencePreparationOldCursorStep ring root z e)
        (generatedGoodStep hn ring root z e hz)

/-- The actual initial-cut ancestry history, for every finite scheduler word. -/
theorem generatedHistory {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n)
    (hr : (N root).l = true)
    (hu : ∀ i : Fin n, (N i).l = true → i = root)
    (hp : PPlus ring N) (w : List (Fin n)) :
    GeneratedGood ring root
      (LDSinkBoundedKernel.run (referencePreparationOldCursorStep ring root)
        (N, (referencePreparationInitialOldLabels N, 0)) w) := by
  exact generatedGoodRun hn ring root w _
    ⟨hr, hu, hp, initialGeneratedInvariant ring root N⟩

/-- Physical stopping target of stage two; fresh bullets are included. -/
def BulletFree {n : Nat} (N : TripleNativeState n) : Prop :=
  ∀ i : Fin n, (N i).b = (0 : Fin 3)

def SingleAt {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n) (p : Nat) : Prop :=
  p < n ∧ (N (PPL.shiftRight ring root p)).b ≠ (0 : Fin 3) ∧
  (∀ i : Fin n, i ≠ PPL.shiftRight ring root p → (N i).b = (0 : Fin 3)) ∧
  ZeroTrail ring root N p

/-- At the genuine no-old-label cut every physical bullet is generated. -/
theorem retiredShape {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n) (mask : Fin n → Bool)
    (hg : GeneratedInvariant ring root N mask) (hm : ∀ i : Fin n, mask i = false) :
    BulletFree N ∨ ∃ p : Nat, SingleAt ring root N p := by
  classical
  by_cases hex : ∃ i : Fin n, (N i).b ≠ (0 : Fin 3)
  · obtain ⟨i, hi⟩ := hex
    have hgi : GeneratedAt N mask i := ⟨hi, hm i⟩
    obtain ⟨p, hp, hs, ht⟩ := hg.1 i hgi
    right
    refine ⟨p, hp, ?_, ?_, ht⟩
    · rw [← hs]
      exact hi
    · intro j hj
      by_cases hb : (N j).b = (0 : Fin 3)
      · exact hb
      · have heq : j = i := hg.2 j i ⟨hb, hm j⟩ hgi
        exact False.elim (hj (heq.trans hs))
  · left
    intro i
    by_cases hb : (N i).b = (0 : Fin 3)
    · exact hb
    · exact False.elim (hex ⟨i, hb⟩)

/-- A non-host service cannot move or create the sole bullet. -/
theorem singleStay {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n) (p : Nat) (e : Fin n)
    (hu : ∀ i : Fin n, (N i).l = true → i = root)
    (hs : SingleAt ring root N p) (he : e ≠ PPL.shiftRight ring root p) :
    SingleAt ring root (nativeE ring N e) p := by
  have hz := trailRootZero ring root N p hs.2.2.2
  have hpair := sealed_prep_actual_old_pair ring N e (rightNe hn ring e)
  have hezero := hs.2.2.1 e he
  have hrow := (literalFacts (N e) (N (ring.rightNeighbor e))).nofire_bullet
    (noFire N root hu hz e) (noFire N root hu hz (ring.rightNeighbor e))
  have hright : (certLiteralEPair (N e) (N (ring.rightNeighbor e))).2.b =
      (N (ring.rightNeighbor e)).b := by
    by_cases hyl : (N (ring.rightNeighbor e)).l = true <;>
    by_cases hyb : (N (ring.rightNeighbor e)).b = (0 : Fin 3) <;>
    simpa [hyl, hyb, hezero] using hrow
  have hsame : ∀ i : Fin n, (nativeE ring N e i).b = (N i).b := by
    intro i
    by_cases hi : i = e
    · rw [hi, hpair.1, (literalFacts (N e) (N (ring.rightNeighbor e))).source_empty, hezero]
    · by_cases hj : i = ring.rightNeighbor e
      · rw [hj, hpair.2]
        exact hright
      · rw [frame ring N e i hi hj]
  refine ⟨hs.1, ?_, ?_, ?_⟩
  · rw [hsame]
    exact hs.2.1
  · intro i hi
    rw [hsame]
    exact hs.2.2.1 i hi
  · exact trailStay hn ring root N p e hs.1 hu hs.2.2.2 (Ne.symm he)

/-- The host's outgoing service advances one offset, or absorbs
at the leader on the final edge. The next bullet cannot be a fresh firing. -/
theorem singleNominated {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n) (p : Nat)
    (hr : (N root).l = true)
    (hu : ∀ i : Fin n, (N i).l = true → i = root)
    (hs : SingleAt ring root N p) :
    BulletFree (nativeE ring N (PPL.shiftRight ring root p)) ∨
    SingleAt ring root (nativeE ring N (PPL.shiftRight ring root p)) (p + 1) := by
  have hz := trailRootZero ring root N p hs.2.2.2
  have hne := rightNe hn ring (PPL.shiftRight ring root p)
  have hpair := sealed_prep_actual_old_pair ring N (PPL.shiftRight ring root p) hne
  have hjzero := hs.2.2.1 (ring.rightNeighbor (PPL.shiftRight ring root p)) hne
  have hrow := (literalFacts (N (PPL.shiftRight ring root p))
    (N (ring.rightNeighbor (PPL.shiftRight ring root p)))).nofire_bullet
    (noFire N root hu hz _) (noFire N root hu hz _)
  by_cases hlast : p + 1 = n
  · have hj : ring.rightNeighbor (PPL.shiftRight ring root p) = root := by
      rw [← referencePreparationShiftSucc, hlast, shiftFull]
    have hright : (certLiteralEPair (N (PPL.shiftRight ring root p))
        (N (ring.rightNeighbor (PPL.shiftRight ring root p)))).2.b = (0 : Fin 3) := by
      have hlead : (N (ring.rightNeighbor (PPL.shiftRight ring root p))).l = true := by
        rw [hj]
        exact hr
      simpa only [if_pos hlead, hjzero] using hrow
    left
    intro i
    by_cases hi : i = PPL.shiftRight ring root p
    · rw [hi, hpair.1]
      exact (literalFacts _ _).source_empty
    · by_cases hjj : i = ring.rightNeighbor (PPL.shiftRight ring root p)
      · rw [hjj, hpair.2]
        exact hright
      · rw [frame ring N (PPL.shiftRight ring root p) i hi hjj]
        exact hs.2.2.1 i hi
  · have hnext : p + 1 < n := by have hp := hs.1; omega
    have hj : ring.rightNeighbor (PPL.shiftRight ring root p) =
        PPL.shiftRight ring root (p + 1) := (referencePreparationShiftSucc ring root p).symm
    have hyl : (N (ring.rightNeighbor (PPL.shiftRight ring root p))).l = false := by
      apply follower N root _ hu
      rw [hj]
      exact referencePreparation_sealed_site_ne ring root (p + 1) (by omega) hnext
    have hright : (certLiteralEPair (N (PPL.shiftRight ring root p))
        (N (ring.rightNeighbor (PPL.shiftRight ring root p)))).2.b =
        (N (PPL.shiftRight ring root p)).b := by
      simpa [hyl, hjzero] using hrow
    right
    refine ⟨hnext, ?_, ?_, trailAdvance hn ring root N p hnext hu hs.2.1 hs.2.2.2⟩
    · rw [← hj, hpair.2, hright]
      exact hs.2.1
    · intro i hi
      by_cases hsrc : i = PPL.shiftRight ring root p
      · rw [hsrc, hpair.1]
        exact (literalFacts _ _).source_empty
      · have hdst : i ≠ ring.rightNeighbor (PPL.shiftRight ring root p) := by
          rw [hj]
          exact hi
        rw [frame ring N (PPL.shiftRight ring root p) i hsrc hdst]
        exact hs.2.2.1 i hsrc

private theorem drainShapeStep {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (z : ReferencePreparationOldCursorState n) (e : Fin n)
    (hr : (z.1 root).l = true)
    (hu : ∀ i : Fin n, (z.1 i).l = true → i = root)
    (hs : SingleAt ring root z.1 z.2.2) :
    BulletFree (referencePreparationOldCursorStep ring root z e).1 ∨
    SingleAt ring root (referencePreparationOldCursorStep ring root z e).1
      (referencePreparationOldCursorStep ring root z e).2.2 := by
  change BulletFree (nativeE ring z.1 e) ∨
    SingleAt ring root (nativeE ring z.1 e)
      (if z.2.2 < n then if e = PPL.shiftRight ring root z.2.2 then z.2.2 + 1 else z.2.2 else z.2.2)
  rw [if_pos hs.1]
  by_cases he : e = PPL.shiftRight ring root z.2.2
  · rw [if_pos he, he]
    exact singleNominated hn ring root z.1 z.2.2 hr hu hs
  · rw [if_neg he]
    exact Or.inr (singleStay hn ring root z.1 z.2.2 e hu hs he)

/-- Same-scheduler comparison with the remaining forward cursor clock.
The native target stops immediately, so no closure of bullet-freeness is assumed. -/
theorem drainCostLeClock {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n) (root : Fin n) :
    ∀ (T : Nat) (z : ReferencePreparationOldCursorState n),
      (z.1 root).l = true →
      (∀ i : Fin n, (z.1 i).l = true → i = root) →
      PPlus ring z.1 →
      (BulletFree z.1 ∨ SingleAt ring root z.1 z.2.2) →
      costNumerator (nativeE ring) BulletFree z.1 T ≤
      costNumerator (referencePreparationOldCursorStep ring root)
        referencePreparationOldCursorDone z T := by
  classical
  intro T
  induction T with
  | zero =>
      intro z hr hu hp hs
      simp only [costNumerator_zero]
      exact Nat.le_refl 0
  | succ T ih =>
      intro z hr hu hp hs
      by_cases hf : BulletFree z.1
      · rw [costNumerator_terminal (nativeE ring) BulletFree z.1 hf (T + 1)]
        exact Nat.zero_le _
      · have hsingle : SingleAt ring root z.1 z.2.2 := by
          rcases hs with hfree | hsingle
          · exact False.elim (hf hfree)
          · exact hsingle
        have hnotdone : ¬ referencePreparationOldCursorDone z := by
          change ¬ n ≤ z.2.2
          have hlt := hsingle.1
          omega
        rw [costNumerator_succ (nativeE ring) BulletFree z.1 hf T,
          costNumerator_succ (referencePreparationOldCursorStep ring root)
            referencePreparationOldCursorDone z hnotdone T]
        have hsum := ofFn_sum_le
          (fun e : Fin n => costNumerator (nativeE ring) BulletFree (nativeE ring z.1 e) T)
          (fun e : Fin n => costNumerator (referencePreparationOldCursorStep ring root)
            referencePreparationOldCursorDone (referencePreparationOldCursorStep ring root z e) T)
          (by
            intro e
            have hfixed := CandidateNativeProof.leader_fixed (by omega : 3 ≤ n)
              ring z.1 e root hr hu hp
            exact ih (referencePreparationOldCursorStep ring root z e)
              hfixed.1 hfixed.2.1
              (nativeE_preserves_PPlus (by omega : 3 ≤ n) ring z.1 e hp)
              (drainShapeStep hn ring root z e hr hu hsingle))
        exact Nat.add_le_add_left hsum _

/-- Stage two for a single bullet with its inclusive zero trail.
The sharper remaining quota is n-p; this theorem uses the uniform n bound. -/
theorem singleDrainCost {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n) (p : Nat)
    (hr : (N root).l = true)
    (hu : ∀ i : Fin n, (N i).l = true → i = root)
    (hp : PPlus ring N) (hs : SingleAt ring root N p) (T : Nat) :
    costNumerator (nativeE ring) BulletFree N T ≤ n ^ T * n ^ 2 := by
  have hcompare := drainCostLeClock hn ring root T
    (N, ((fun _ : Fin n => false), p)) hr hu hp (Or.inr hs)
  have hclock := referencePreparationOldCursorClockCost ring root
    (N, ((fun _ : Fin n => false), p)) T
  have h := Nat.le_trans hcompare hclock
  have hcap : n * (n - p) ≤ n ^ 2 := by
    calc
      n * (n - p) ≤ n * n := Nat.mul_le_mul_left n (Nat.sub_le n p)
      _ = n ^ 2 := by rw [Nat.pow_two]
  exact Nat.le_trans h (Nat.mul_le_mul_left (n ^ T) hcap)

/-- A cut predicate carrying the provenance that an arbitrary false mask lacks. -/
def Retired {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (z : ReferencePreparationOldCursorState n) : Prop :=
  referencePreparationOldCursorLabelFree z ∧ GeneratedGood ring root z

/-- Exact invariant-qualified second-stage premise. The cursor in z need
not be the drain cursor: projection removes it, and the drain proof starts
its own analytical cursor at the sole bullet's current offset. -/
theorem secondStageCost {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (z : ReferencePreparationOldCursorState n)
    (hz : Retired ring root z) (T : Nat) :
    costNumerator (referencePreparationOldCursorStep ring root)
      (fun x => BulletFree x.1) z T ≤ n ^ T * n ^ 2 := by
  rw [referencePreparationOldCursorPhysicalCostEq ring root BulletFree z T]
  rcases retiredShape ring root z.1 z.2.1 hz.2.2.2.2 hz.1 with hfree | hsingle
  · rw [costNumerator_terminal (nativeE ring) BulletFree z.1 hfree T]
    exact Nat.zero_le _
  · obtain ⟨p, hp⟩ := hsingle
    exact singleDrainCost hn ring root z.1 p hz.2.1 hz.2.2.1 hz.2.2.2.1 hp T

theorem secondStageOrCost {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (P : TripleNativeState n → Prop)
    (z : ReferencePreparationOldCursorState n) (hz : Retired ring root z) (T : Nat) :
    costNumerator (referencePreparationOldCursorStep ring root)
      (fun x => BulletFree x.1 ∨ P x.1) z T ≤ n ^ T * n ^ 2 := by
  exact Nat.le_trans
    (Prob.costNumerator_target_mono (referencePreparationOldCursorStep ring root)
      (fun x => BulletFree x.1) (fun x => BulletFree x.1 ∨ P x.1)
      (by intro x hx; exact Or.inl hx) z T)
    (secondStageCost hn ring root z hz T)

private theorem costLeOnInvariant {n : Nat} {S : Type}
    (next : S → Fin n → S) (I P Q : S → Prop)
    (hstep : ∀ x, I x → ∀ e, I (next x e))
    (hstop : ∀ x, I x → Q x → P x) :
    ∀ T x, I x → costNumerator next P x T ≤ costNumerator next Q x T := by
  classical
  intro T
  induction T with
  | zero =>
      intro x hx
      simp only [costNumerator_zero]
      exact Nat.le_refl 0
  | succ T ih =>
      intro x hx
      by_cases hp : P x
      · rw [costNumerator_terminal next P x hp (T + 1)]
        exact Nat.zero_le _
      · have hq : ¬ Q x := by intro h; exact hp (hstop x hx h)
        rw [costNumerator_succ next P x hp T, costNumerator_succ next Q x hq T]
        exact Nat.add_le_add_left
          (ofFn_sum_le
            (fun e : Fin n => costNumerator next P (next x e) T)
            (fun e : Fin n => costNumerator next Q (next x e) T)
            (fun e => ih (next x e) (hstep x hx e))) _

/-- Strengthening the first cut by the reached generated invariant costs
nothing. This repairs the domain of the second-stage consumer. -/
theorem firstRetiredCost {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n)
    (hr : (N root).l = true)
    (hu : ∀ i : Fin n, (N i).l = true → i = root)
    (hp : PPlus ring N) (T : Nat) :
    costNumerator (referencePreparationOldCursorStep ring root) (Retired ring root)
      (N, (referencePreparationInitialOldLabels N, 0)) T ≤ n ^ T * n ^ 2 := by
  have hinitial : ReferencePreparationOldCursorGood ring root
      (N, (referencePreparationInitialOldLabels N, 0)) ∧
      GeneratedGood ring root (N, (referencePreparationInitialOldLabels N, 0)) := by
    constructor
    · refine ⟨hr, hu, hp, ?_⟩
      intro k hk
      exact absurd hk (Nat.not_lt_zero k)
    · exact ⟨hr, hu, hp, initialGeneratedInvariant ring root N⟩
  have hcompare := costLeOnInvariant (referencePreparationOldCursorStep ring root)
    (fun z => ReferencePreparationOldCursorGood ring root z ∧ GeneratedGood ring root z)
    (Retired ring root) referencePreparationOldCursorDone
    (by
      intro z hz e
      exact ⟨referencePreparationOldCursorGoodStep hn ring root z e hz.1,
        generatedGoodStep hn ring root z e hz.2⟩)
    (by
      intro z hz hd
      exact ⟨referencePreparationOldCursorDoneNoOld ring root z hz.1 hd, hz.2⟩)
    T (N, (referencePreparationInitialOldLabels N, 0)) hinitial
  have hclock := referencePreparationOldCursorClockCost ring root
    (N, (referencePreparationInitialOldLabels N, 0)) T
  have h := Nat.le_trans hcompare hclock
  simpa only [Nat.sub_zero, Nat.pow_two] using h

/-- The first two physical cuts composed on one scheduler. This does not
claim readiness, all-signals-one, or candidate retirement. -/
theorem firstTwoStagesCost {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n)
    (hr : (N root).l = true)
    (hu : ∀ i : Fin n, (N i).l = true → i = root)
    (hp : PPlus ring N) (T : Nat) :
    costNumerator (nativeE ring) BulletFree N T ≤ n ^ T * (2 * n ^ 2) := by
  have hfirst : ∀ U,
      costNumerator (referencePreparationOldCursorStep ring root)
        (fun z => Retired ring root z ∨ BulletFree z.1)
        (N, (referencePreparationInitialOldLabels N, 0)) U ≤ n ^ U * n ^ 2 := by
    intro U
    exact Nat.le_trans
      (Prob.costNumerator_target_mono (referencePreparationOldCursorStep ring root)
        (Retired ring root) (fun z => Retired ring root z ∨ BulletFree z.1)
        (by intro z hz; exact Or.inl hz)
        (N, (referencePreparationInitialOldLabels N, 0)) U)
      (firstRetiredCost hn ring root N hr hu hp U)
  have h := Prob.costNumerator_stage_le (referencePreparationOldCursorStep ring root)
    (N, (referencePreparationInitialOldLabels N, 0))
    (Retired ring root) (fun z => BulletFree z.1) (n ^ 2) (n ^ 2)
    hfirst (by intro z hz U; exact secondStageCost hn ring root z hz U) T
  have heq : n ^ 2 + n ^ 2 = 2 * n ^ 2 := by omega
  rw [heq, referencePreparationOldCursorPhysicalCostEq ring root BulletFree
    (N, (referencePreparationInitialOldLabels N, 0)) T] at h
  exact h

end ReferencePreparationTrail
end L3

/-!
First readiness, fresh firing, and the exact absorption cut.
All clocks execute nativeE on
EVERY selected edge. A stopped invariant is used only before its
physical target; readiness and bullet-freeness are not claimed closed.
-/

namespace L3
namespace ReferencePreparationTrail

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The same protected singleton at the original root. -/
def Rooted {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n) : Prop :=
  (N root).l = true ∧
  (∀ i : Fin n, (N i).l = true → i = root) ∧ PPlus ring N

theorem rootedStep {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n) (e : Fin n)
    (h : Rooted ring root N) : Rooted ring root (nativeE ring N e) := by
  have hf := CandidateNativeProof.leader_fixed (by omega : 3 ≤ n)
    ring N e root h.1 h.2.1 h.2.2
  exact ⟨hf.1, hf.2.1, nativeE_preserves_PPlus (by omega : 3 ≤ n) ring N e h.2.2⟩

/-- Literal OLD-pair equations when neither endpoint fires and both
old bullet fields are empty. The first new readiness signal is too late
to trigger a firing in this same interaction. -/
private theorem emptyQuietPair (x y : CertNative)
    (hx : x.b = (0 : Fin 3)) (hy : y.b = (0 : Fin 3))
    (hfx : ¬ (x.l = true ∧ x.sg = true))
    (hfy : ¬ (y.l = true ∧ y.sg = true)) :
    (certLiteralEPair x y).1.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).2.b = (0 : Fin 3) ∧
    (certLiteralEPair x y).1.sg = (x.sg || y.sg || y.l) ∧
    (certLiteralEPair x y).2.sg = y.sg := by
  cases hxl : x.l <;> cases hyl : y.l <;>
  cases hxs : x.sg <;> cases hys : y.sg <;>
  simp [certLiteralEPair, certFinThree, hx, hy, hxl, hyl, hxs, hys] at *

/-- Bullet-free and signal-monotone on every quiet selected pair. -/
theorem emptyQuietStep {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (N : TripleNativeState n) (e : Fin n) (hb : BulletFree N)
    (hx : ¬ ((N e).l = true ∧ (N e).sg = true))
    (hy : ¬ ((N (ring.rightNeighbor e)).l = true ∧
      (N (ring.rightNeighbor e)).sg = true)) :
    BulletFree (nativeE ring N e) ∧
    (∀ i : Fin n, (N i).sg = true → (nativeE ring N e i).sg = true) ∧
    (nativeE ring N e e).sg =
      ((N e).sg || (N (ring.rightNeighbor e)).sg || (N (ring.rightNeighbor e)).l) := by
  have hp := sealed_prep_actual_old_pair ring N e (rightNe hn ring e)
  have hrow := emptyQuietPair (N e) (N (ring.rightNeighbor e))
    (hb e) (hb (ring.rightNeighbor e)) hx hy
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = e
    · rw [hi, hp.1]
      exact hrow.1
    · by_cases hj : i = ring.rightNeighbor e
      · rw [hj, hp.2]
        exact hrow.2.1
      · rw [frame ring N e i hi hj]
        exact hb i
  · intro i hs
    by_cases hi : i = e
    · rw [hi] at hs
      rw [hi, hp.1, hrow.2.2.1]
      simp [hs]
    · by_cases hj : i = ring.rightNeighbor e
      · rw [hj] at hs
        rw [hj, hp.2, hrow.2.2.2]
        exact hs
      · rw [frame ring N e i hi hj]
        exact hs
  · rw [hp.1]
    exact hrow.2.2.1

/-- H.3, including the step that FIRST makes the root ready. -/
theorem beforeReadyStep {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n) (e : Fin n)
    (hr : Rooted ring root N) (hb : BulletFree N)
    (hz : (N root).sg = false) :
    (∀ i : Fin n, ¬ ((N i).l = true ∧ (N i).sg = true)) ∧
    BulletFree (nativeE ring N e) ∧
    (∀ i : Fin n, (N i).sg = true → (nativeE ring N e i).sg = true) := by
  have hq := noFire N root hr.2.1 hz
  have hs := emptyQuietStep hn ring N e hb (hq e) (hq (ring.rightNeighbor e))
  exact ⟨hq, hs.1, hs.2.1⟩

/-- Readiness is a physical target containing bullet-freeness. -/
def ReadyCut {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n) : Prop :=
  Rooted ring root N ∧ BulletFree N ∧ (N root).sg = true

/-- Remaining backward services. A cursor value c nominates e_(c-1).
Starting at n gives e_(n-1),...,e_0 with arbitrary interleavings. -/
def readinessStep {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (z : TripleNativeState n × Nat) (e : Fin n) : TripleNativeState n × Nat :=
  (nativeE ring z.1 e,
    if z.2 = 0 then 0 else
      if e = PPL.shiftRight ring root (z.2 - 1) then z.2 - 1 else z.2)

def ReadinessDone {n : Nat} (z : TripleNativeState n × Nat) : Prop := z.2 = 0

def ReadinessGood {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (z : TripleNativeState n × Nat) : Prop :=
  Rooted ring root z.1 ∧ BulletFree z.1 ∧ z.2 ≤ n ∧
    ∀ k : Nat, z.2 ≤ k → k < n → (z.1 (PPL.shiftRight ring root k)).sg = true

private theorem readinessDrop {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (z : TripleNativeState n × Nat) (h : ¬ ReadinessDone z) :
    (readinessStep ring root z (PPL.shiftRight ring root (z.2 - 1))).2 + 1 ≤ z.2 := by
  have hz : z.2 ≠ 0 := h
  simp only [readinessStep, if_neg hz, if_pos rfl, ↓reduceIte]
  omega

private theorem readinessNonincrease {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (z : TripleNativeState n × Nat) (_h : ¬ ReadinessDone z) (e : Fin n) :
    (readinessStep ring root z e).2 ≤ z.2 := by
  by_cases hz : z.2 = 0
  · simp only [readinessStep, if_pos hz]
    exact Nat.zero_le _
  · by_cases he : e = PPL.shiftRight ring root (z.2 - 1)
    · simp only [readinessStep, if_neg hz, if_pos he]
      exact Nat.sub_le _ _
    · simp only [readinessStep, if_neg hz, if_neg he]
      exact Nat.le_refl _

theorem readinessClockCost {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (z : TripleNativeState n × Nat) (T : Nat) :
    costNumerator (readinessStep ring root) ReadinessDone z T ≤ n ^ T * (n * z.2) := by
  exact Prob.costNumerator_le_of_nominated_edge (readinessStep ring root)
    ReadinessDone (fun x => x.2)
    (fun x => PPL.shiftRight ring root (x.2 - 1))
    (readinessDrop ring root) (readinessNonincrease ring root) z T

private theorem readinessDoneReady {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (z : TripleNativeState n × Nat) (h : ReadinessGood ring root z)
    (hd : ReadinessDone z) : ReadyCut ring root z.1 := by
  have hc : z.2 = 0 := hd
  have hs := h.2.2.2 0 (by omega) ring.hn
  rw [referencePreparationShiftZero] at hs
  exact ⟨h.1, h.2.1, hs⟩

private theorem backwardNominatedSignal {n : Nat} (hn : 5 ≤ n)
    (ring : DirectedRing n) (root : Fin n) (N : TripleNativeState n)
    (c : Nat) (hc : 0 < c) (hcn : c ≤ n)
    (hr : Rooted ring root N) (hb : BulletFree N) (hz : (N root).sg = false)
    (hs : ∀ k : Nat, c ≤ k → k < n → (N (PPL.shiftRight ring root k)).sg = true) :
    (nativeE ring N (PPL.shiftRight ring root (c - 1))
      (PPL.shiftRight ring root (c - 1))).sg = true := by
  have hq := noFire N root hr.2.1 hz
  have hp := emptyQuietStep hn ring N (PPL.shiftRight ring root (c - 1)) hb
    (hq _) (hq _)
  have hindex : (c - 1) + 1 = c := by omega
  have hj : ring.rightNeighbor (PPL.shiftRight ring root (c - 1)) =
      PPL.shiftRight ring root c := by
    rw [← referencePreparationShiftSucc, hindex]
  rw [hp.2.2, hj]
  by_cases hlast : c = n
  · rw [hlast, shiftFull]
    simp [hr.1]
  · have hsig := hs c (Nat.le_refl c) (by omega)
    simp [hsig]

/-- Before first readiness the suffix of already serviced sites remains
one, even with arbitrary holes in the as-yet-unserviced prefix. -/
theorem readinessGoodStep {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (z : TripleNativeState n × Nat) (e : Fin n)
    (h : ReadinessGood ring root z) (hnot : ¬ ReadyCut ring root z.1) :
    ReadinessGood ring root (readinessStep ring root z e) := by
  have hz : (z.1 root).sg = false := by
    cases hs : (z.1 root).sg with
    | false => rfl
    | true => exact False.elim (hnot ⟨h.1, h.2.1, hs⟩)
  have hc : z.2 ≠ 0 := by
    intro heq
    exact hnot (readinessDoneReady ring root z h heq)
  have hq := noFire z.1 root h.1.2.1 hz
  have hp := emptyQuietStep hn ring z.1 e h.2.1 (hq e) (hq (ring.rightNeighbor e))
  have hr := rootedStep hn ring root z.1 e h.1
  by_cases he : e = PPL.shiftRight ring root (z.2 - 1)
  · have hi : (readinessStep ring root z e).2 = z.2 - 1 := by
      simp only [readinessStep, if_neg hc, if_pos he]
    refine ⟨hr, hp.1, ?_, ?_⟩
    · rw [hi]
      exact Nat.le_trans (Nat.sub_le _ _) h.2.2.1
    · intro k hk hkn
      rw [hi] at hk
      change (nativeE ring z.1 e (PPL.shiftRight ring root k)).sg = true
      by_cases hke : k = z.2 - 1
      · rw [hke, he]
        exact backwardNominatedSignal hn ring root z.1 z.2 (by omega)
          h.2.2.1 h.1 h.2.1 hz h.2.2.2
      · exact hp.2.1 _ (h.2.2.2 k (by omega) hkn)
  · have hi : (readinessStep ring root z e).2 = z.2 := by
      simp only [readinessStep, if_neg hc, if_neg he]
    refine ⟨hr, hp.1, ?_, ?_⟩
    · rw [hi]
      exact h.2.2.1
    · intro k hk hkn
      rw [hi] at hk
      exact hp.2.1 _ (h.2.2.2 k hk hkn)

/-- The physical first ready-and-bullet-free cut occurs no later than
completion of the backward cursor; no independence is assumed. -/
theorem readinessCostLeClock {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) : ∀ T (z : TripleNativeState n × Nat),
    ReadinessGood ring root z →
    costNumerator (nativeE ring) (ReadyCut ring root) z.1 T ≤
    costNumerator (readinessStep ring root) ReadinessDone z T := by
  classical
  intro T
  induction T with
  | zero =>
      intro z hz
      simp only [costNumerator_zero]
      exact Nat.le_refl 0
  | succ T ih =>
      intro z hz
      by_cases hr : ReadyCut ring root z.1
      · rw [costNumerator_terminal (nativeE ring) (ReadyCut ring root) z.1 hr (T + 1)]
        exact Nat.zero_le _
      · have hd : ¬ ReadinessDone z := by
          intro hdone
          exact hr (readinessDoneReady ring root z hz hdone)
        rw [costNumerator_succ (nativeE ring) (ReadyCut ring root) z.1 hr T,
          costNumerator_succ (readinessStep ring root) ReadinessDone z hd T]
        exact Nat.add_le_add_left
          (ofFn_sum_le
            (fun e : Fin n => costNumerator (nativeE ring) (ReadyCut ring root) (nativeE ring z.1 e) T)
            (fun e : Fin n => costNumerator (readinessStep ring root) ReadinessDone (readinessStep ring root z e) T)
            (fun e => ih (readinessStep ring root z e) (readinessGoodStep hn ring root z e hz hr))) _

/-- H.3 with arbitrary initial signal gaps, including readiness at time
zero. The target includes the SAME root and no physical bullet. -/
theorem readinessCost {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n)
    (hr : Rooted ring root N) (hb : BulletFree N) (T : Nat) :
    costNumerator (nativeE ring) (ReadyCut ring root) N T ≤ n ^ T * n ^ 2 := by
  have hg : ReadinessGood ring root (N, n) := by
    refine ⟨hr, hb, Nat.le_refl n, ?_⟩
    intro k hk hkn
    change n ≤ k at hk
    omega
  have h := Nat.le_trans (readinessCostLeClock hn ring root T (N, n) hg)
    (readinessClockCost ring root (N, n) T)
  simpa only [Nat.pow_two] using h

/-- The next leader-incident service has produced the sole trailed
bullet. The analytical host offset is not part of the native protocol. -/
def FiredCut {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n) : Prop :=
  Rooted ring root N ∧ ∃ p : Nat, SingleAt ring root N p

private theorem shiftOne {n : Nat} (ring : DirectedRing n) (root : Fin n) :
    PPL.shiftRight ring root 1 = ring.rightNeighbor root := by
  rfl

/-- The outgoing ready service creates exactly one live bullet at site
one; arbitrary follower signal gaps do not affect the new zero trail. -/
theorem freshOutgoing {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n) (h : ReadyCut ring root N) :
    SingleAt ring root (nativeE ring N root) 1 ∧
    (nativeE ring N root (PPL.shiftRight ring root 1)).b = (2 : Fin 3) := by
  have hne := rightNe hn ring root
  have hyl := follower N root (ring.rightNeighbor root) h.1.2.1 hne
  have hp := sealed_prep_actual_old_pair ring N root hne
  have hz := (literalFacts (N root) (N (ring.rightNeighbor root))).fresh_out_zero
    h.1.1 h.2.2 hyl
  have hb : (nativeE ring N root (ring.rightNeighbor root)).b = (2 : Fin 3) := by
    rw [hp.2]
    simp [certLiteralEPair, certFinThree, h.1.1, h.2.2, hyl, h.2.1 (ring.rightNeighbor root)]
  have hsource : (nativeE ring N root root).b = (0 : Fin 3) := by
    rw [hp.1]
    exact (literalFacts _ _).source_empty
  refine ⟨⟨by omega, ?_, ?_, ?_⟩, ?_⟩
  · rw [shiftOne, hb]
    intro heq
    have hv := congrArg Fin.val heq
    change 2 = 0 at hv
    omega
  · intro i hi
    have hj : i ≠ ring.rightNeighbor root := by
      simpa only [shiftOne] using hi
    by_cases he : i = root
    · rw [he]
      exact hsource
    · rw [frame ring N root i he hj]
      exact h.2.1 i
  · intro k hk
    have hc : k = 0 ∨ k = 1 := by omega
    rcases hc with he | he
    · rw [he, referencePreparationShiftZero, hp.1]
      exact hz.1
    · rw [he, shiftOne, hp.2]
      exact hz.2
  · rw [shiftOne]
    exact hb

/-- The incoming ready service creates exactly one dummy at the root. -/
theorem freshIncoming {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root e : Fin n) (N : TripleNativeState n) (h : ReadyCut ring root N)
    (hj : ring.rightNeighbor e = root) :
    SingleAt ring root (nativeE ring N e) 0 ∧
    (nativeE ring N e root).b = (1 : Fin 3) := by
  have hne : root ≠ e := by
    rw [← hj]
    exact rightNe hn ring e
  have hxl := follower N root e h.1.2.1 (Ne.symm hne)
  have hp := sealed_prep_actual_old_pair ring N e (rightNe hn ring e)
  have hr : nativeE ring N e root = (certLiteralEPair (N e) (N root)).2 := by
    have hh := hp.2
    rw [hj] at hh
    exact hh
  have hb : (nativeE ring N e root).b = (1 : Fin 3) := by
    rw [hr]
    simp [certLiteralEPair, certFinThree, hxl, h.2.1 e, h.1.1, h.2.2]
  have hs : (nativeE ring N e root).sg = false := by
    rw [hr]
    exact (literalFacts (N e) (N root)).leader_zero h.1.1
  refine ⟨⟨ring.hn, ?_, ?_, ?_⟩, hb⟩
  · rw [referencePreparationShiftZero, hb]
    intro heq
    have hv := congrArg Fin.val heq
    change 1 = 0 at hv
    omega
  · intro i hi
    have hir : i ≠ root := by
      simpa only [referencePreparationShiftZero] using hi
    by_cases he : i = e
    · rw [he, hp.1]
      exact (literalFacts _ _).source_empty
    · have hij : i ≠ ring.rightNeighbor e := by
        rw [hj]
        exact hir
      rw [frame ring N e i he hij]
      exact h.2.1 i
  · intro k hk
    have hkz : k = 0 := by omega
    rw [hkz, referencePreparationShiftZero]
    exact hs

private theorem rightLeft {n : Nat} (ring : DirectedRing n) (root : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor root) = root := by
  apply Fin.ext
  change (((root.val + n - 1) % n + 1) % n) = root.val
  rw [Nat.mod_add_mod]
  have hn := ring.hn
  have heq : root.val + n - 1 + 1 = root.val + n := by omega
  rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt root.isLt]

/-- Before the first incident edge, readiness and bullet-freeness persist. -/
theorem readyNonincident {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n) (e : Fin n)
    (h : ReadyCut ring root N) (he : e ≠ root)
    (hj : ring.rightNeighbor e ≠ root) : ReadyCut ring root (nativeE ring N e) := by
  have hx := follower N root e h.1.2.1 he
  have hy := follower N root (ring.rightNeighbor e) h.1.2.1 hj
  have hfx : ¬ ((N e).l = true ∧ (N e).sg = true) := by simp [hx]
  have hfy : ¬ ((N (ring.rightNeighbor e)).l = true ∧
      (N (ring.rightNeighbor e)).sg = true) := by simp [hy]
  have hb := (emptyQuietStep hn ring N e h.2.1 hfx hfy).1
  refine ⟨rootedStep hn ring root N e h.1, hb, ?_⟩
  rw [frame ring N e root (Ne.symm he) (Ne.symm hj)]
  exact h.2.2

/-- Physical fresh-firing target versus the existing two-port flag clock. -/
theorem freshCostLeIncident {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) : ∀ T (N : TripleNativeState n), ReadyCut ring root N →
    costNumerator (nativeE ring) (FiredCut ring root) N T ≤
    costNumerator (referencePreparationIncidentNativeStep ring root)
      (fun z : Bool × TripleNativeState n => z.1 = true) (false, N) T := by
  classical
  intro T
  induction T with
  | zero =>
      intro N hN
      simp only [costNumerator_zero]
      exact Nat.le_refl 0
  | succ T ih =>
      intro N hN
      by_cases hf : FiredCut ring root N
      · rw [costNumerator_terminal (nativeE ring) (FiredCut ring root) N hf (T + 1)]
        exact Nat.zero_le _
      · have hflag : ¬ (fun z : Bool × TripleNativeState n => z.1 = true) (false, N) := by
          intro heq
          cases heq
        rw [costNumerator_succ (nativeE ring) (FiredCut ring root) N hf T,
          costNumerator_succ (referencePreparationIncidentNativeStep ring root)
            (fun z : Bool × TripleNativeState n => z.1 = true) (false, N) hflag T]
        apply Nat.add_le_add_left
        apply ofFn_sum_le
        intro e
        by_cases he : e = root
        · have hfire : FiredCut ring root (nativeE ring N e) := by
            rw [he]
            exact ⟨rootedStep hn ring root N root hN.1, 1, (freshOutgoing hn ring root N hN).1⟩
          rw [costNumerator_terminal (nativeE ring) (FiredCut ring root) (nativeE ring N e) hfire T]
          exact Nat.zero_le _
        · by_cases hb : e = ring.leftNeighbor root
          · have hj : ring.rightNeighbor e = root := by rw [hb, rightLeft]
            have hfire : FiredCut ring root (nativeE ring N e) :=
              ⟨rootedStep hn ring root N e hN.1, 0, (freshIncoming hn ring root e N hN hj).1⟩
            rw [costNumerator_terminal (nativeE ring) (FiredCut ring root) (nativeE ring N e) hfire T]
            exact Nat.zero_le _
          · have hj : ring.rightNeighbor e ≠ root := by
              intro hroot
              have hh : ring.rightNeighbor e = ring.rightNeighbor (ring.leftNeighbor root) :=
                hroot.trans (rightLeft ring root).symm
              exact hb (referencePreparationRightInjective ring hh)
            have hnext := readyNonincident hn ring root N e hN he hj
            simpa only [referencePreparationIncidentNativeStep, referencePreparationIncidentFlagStep,
              if_neg he, if_neg hb] using ih (nativeE ring N e) hnext

/-- Exact n/2 fresh-firing charge, in doubled integer form. -/
theorem freshHalfCost {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n) (h : ReadyCut ring root N) (T : Nat) :
    2 * costNumerator (nativeE ring) (FiredCut ring root) N T ≤ n ^ T * n := by
  exact Nat.le_trans (Nat.mul_le_mul_left 2 (freshCostLeIncident hn ring root T N h))
    (referencePreparationIncidentNativeHalfCost hn ring root N T)

/-- Exact physical state immediately after absorption of the distinguished
bullet, before any later backward signal propagation. -/
def AbsorbedCut {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n) : Prop :=
  Rooted ring root N ∧ BulletFree N ∧
  (N (PPL.shiftRight ring root (n - 1))).sg = true ∧
  ∀ k : Nat, k < n - 1 → (N (PPL.shiftRight ring root k)).sg = false

/-- No premature disappearance on an interior host service. -/
theorem singleForward {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n) (p : Nat)
    (hr : Rooted ring root N) (hs : SingleAt ring root N p) (hnext : p + 1 < n) :
    SingleAt ring root (nativeE ring N (PPL.shiftRight ring root p)) (p + 1) := by
  have hz := trailRootZero ring root N p hs.2.2.2
  have hyl : (N (ring.rightNeighbor (PPL.shiftRight ring root p))).l = false := by
    apply follower N root _ hr.2.1
    rw [← referencePreparationShiftSucc]
    exact referencePreparation_sealed_site_ne ring root (p + 1) (by omega) hnext
  have hno : ((N (PPL.shiftRight ring root p)).l && (N (PPL.shiftRight ring root p)).sg) = false := by
    have hsig := hs.2.2.2 p (Nat.le_refl p)
    simp [hsig]
  have hrow := sealed_prep_push_no_launch_row
    (N (PPL.shiftRight ring root p)) (N (ring.rightNeighbor (PPL.shiftRight ring root p)))
    hno hs.2.1 hyl
  have hp := sealed_prep_actual_old_pair ring N (PPL.shiftRight ring root p)
    (rightNe hn ring (PPL.shiftRight ring root p))
  rcases singleNominated hn ring root N p hr.1 hr.2.1 hs with hf | hsnext
  · have hb := hf (ring.rightNeighbor (PPL.shiftRight ring root p))
    rw [hp.2] at hb
    exact False.elim (hrow.2.2.1 hb)
  · exact hsnext

/-- Terminal native service: all sites were zero, the root does not fire,
and only the final source gets the returning one-signal. -/
theorem lastAbsorption {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n) (p : Nat)
    (hr : Rooted ring root N) (hs : SingleAt ring root N p) (hlast : p + 1 = n) :
    AbsorbedCut ring root (nativeE ring N (PPL.shiftRight ring root p)) := by
  have hpindex : p = n - 1 := by omega
  have hj : ring.rightNeighbor (PPL.shiftRight ring root p) = root := by
    rw [← referencePreparationShiftSucc, hlast, shiftFull]
  have hp := sealed_prep_actual_old_pair ring N (PPL.shiftRight ring root p)
    (rightNe hn ring (PPL.shiftRight ring root p))
  have hrnext := rootedStep hn ring root N (PPL.shiftRight ring root p) hr
  have hfree : BulletFree (nativeE ring N (PPL.shiftRight ring root p)) := by
    rcases singleNominated hn ring root N p hr.1 hr.2.1 hs with hf | hsingle
    · exact hf
    · have hbad := hsingle.1
      omega
  have hyl : (N (ring.rightNeighbor (PPL.shiftRight ring root p))).l = true := by
    rw [hj]
    exact hr.1
  have hsig : (nativeE ring N (PPL.shiftRight ring root p) (PPL.shiftRight ring root p)).sg = true := by
    rcases sealed_prep_terminal_bullet_row
        (N (PPL.shiftRight ring root p)) (N (ring.rightNeighbor (PPL.shiftRight ring root p)))
        hs.2.1 hyl with hdead | halive
    · have hkeep : (nativeE ring N (PPL.shiftRight ring root p)
          (ring.rightNeighbor (PPL.shiftRight ring root p))).l = true := by
        rw [hj]
        exact hrnext.1
      rw [hp.2, hdead] at hkeep
      cases hkeep
    · rw [hp.1]
      exact halive.2
  refine ⟨hrnext, hfree, ?_, ?_⟩
  · rw [← hpindex]
    exact hsig
  · intro k hk
    have hkp : k < p := by omega
    have hsrc : PPL.shiftRight ring root k ≠ PPL.shiftRight ring root p := by
      intro heq
      have hv := shiftInjective ring root k p (by omega) hs.1 heq
      omega
    by_cases hdst : PPL.shiftRight ring root k = ring.rightNeighbor (PPL.shiftRight ring root p)
    · have hz := hs.2.2.2 k (by omega)
      rw [hdst] at hz
      rw [hdst, hp.2]
      exact (literalFacts _ _).responder_zero hz
    · rw [frame ring N (PPL.shiftRight ring root p) (PPL.shiftRight ring root k) hsrc hdst]
      exact hs.2.2.2 k (by omega)

private theorem circulationShapeStep {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (z : ReferencePreparationOldCursorState n) (e : Fin n)
    (hr : Rooted ring root z.1) (hs : SingleAt ring root z.1 z.2.2) :
    AbsorbedCut ring root (referencePreparationOldCursorStep ring root z e).1 ∨
    SingleAt ring root (referencePreparationOldCursorStep ring root z e).1
      (referencePreparationOldCursorStep ring root z e).2.2 := by
  change AbsorbedCut ring root (nativeE ring z.1 e) ∨
    SingleAt ring root (nativeE ring z.1 e)
      (if z.2.2 < n then if e = PPL.shiftRight ring root z.2.2 then z.2.2 + 1 else z.2.2 else z.2.2)
  rw [if_pos hs.1]
  by_cases he : e = PPL.shiftRight ring root z.2.2
  · rw [if_pos he, he]
    by_cases hl : z.2.2 + 1 = n
    · exact Or.inl (lastAbsorption hn ring root z.1 z.2.2 hr hs hl)
    · have hc := hs.1
      exact Or.inr (singleForward hn ring root z.1 z.2.2 hr hs (by omega))
  · rw [if_neg he]
    exact Or.inr (singleStay hn ring root z.1 z.2.2 e hr.2.1 hs he)

/-- The full absorption target, not just bullet-freeness, is reached by
completion of the same remaining host-service cursor. -/
theorem circulationCostLeClock {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) : ∀ T (z : ReferencePreparationOldCursorState n),
    Rooted ring root z.1 →
    (AbsorbedCut ring root z.1 ∨ SingleAt ring root z.1 z.2.2) →
    costNumerator (nativeE ring) (AbsorbedCut ring root) z.1 T ≤
    costNumerator (referencePreparationOldCursorStep ring root) referencePreparationOldCursorDone z T := by
  classical
  intro T
  induction T with
  | zero =>
      intro z hr hs
      simp only [costNumerator_zero]
      exact Nat.le_refl 0
  | succ T ih =>
      intro z hr hs
      by_cases ha : AbsorbedCut ring root z.1
      · rw [costNumerator_terminal (nativeE ring) (AbsorbedCut ring root) z.1 ha (T + 1)]
        exact Nat.zero_le _
      · have hsingle : SingleAt ring root z.1 z.2.2 := by
          rcases hs with hdone | hsingle
          · exact False.elim (ha hdone)
          · exact hsingle
        have hd : ¬ referencePreparationOldCursorDone z := by
          change ¬ n ≤ z.2.2
          have hc := hsingle.1
          omega
        rw [costNumerator_succ (nativeE ring) (AbsorbedCut ring root) z.1 ha T,
          costNumerator_succ (referencePreparationOldCursorStep ring root) referencePreparationOldCursorDone z hd T]
        exact Nat.add_le_add_left
          (ofFn_sum_le
            (fun e : Fin n => costNumerator (nativeE ring) (AbsorbedCut ring root) (nativeE ring z.1 e) T)
            (fun e : Fin n => costNumerator (referencePreparationOldCursorStep ring root)
              referencePreparationOldCursorDone (referencePreparationOldCursorStep ring root z e) T)
            (fun e => ih (referencePreparationOldCursorStep ring root z e)
              (rootedStep hn ring root z.1 e hr)
              (circulationShapeStep hn ring root z e hr hsingle))) _

/-- Complete fresh circulation, including its exact physical signal
pattern after absorption. The number of nominated services is at most n. -/
theorem circulationCost {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n) (h : FiredCut ring root N) (T : Nat) :
    costNumerator (nativeE ring) (AbsorbedCut ring root) N T ≤ n ^ T * n ^ 2 := by
  obtain ⟨p, hp⟩ := h.2
  have hc := circulationCostLeClock hn ring root T
    (N, ((fun _ : Fin n => false), p)) h.1 (Or.inr hp)
  have hk := referencePreparationOldCursorClockCost ring root
    (N, ((fun _ : Fin n => false), p)) T
  have hcap : n * (n - p) ≤ n ^ 2 := by
    calc
      n * (n - p) ≤ n * n := Nat.mul_le_mul_left n (Nat.sub_le n p)
      _ = n ^ 2 := by rw [Nat.pow_two]
  exact Nat.le_trans (Nat.le_trans hc hk) (Nat.mul_le_mul_left (n ^ T) hcap)

/-- First two stages plus H.3, carrying the singleton invariant at the
handoff rather than quantifying over arbitrary bullet-free states. -/
theorem firstThreeStagesCost {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n) (hr : Rooted ring root N) (T : Nat) :
    costNumerator (nativeE ring) (ReadyCut ring root) N T ≤ n ^ T * (3 * n ^ 2) := by
  have hfirst : ∀ U, costNumerator (nativeE ring)
      (fun x => (Rooted ring root x ∧ BulletFree x) ∨ ReadyCut ring root x) N U ≤
      n ^ U * (2 * n ^ 2) := by
    intro U
    have hstrength := costLeOnInvariant (nativeE ring) (Rooted ring root)
      (fun x => Rooted ring root x ∧ BulletFree x) BulletFree
      (by intro x hx e; exact rootedStep hn ring root x e hx)
      (by intro x hx hb; exact ⟨hx, hb⟩) U N hr
    have hmono := Prob.costNumerator_target_mono (nativeE ring)
      (fun x => Rooted ring root x ∧ BulletFree x)
      (fun x => (Rooted ring root x ∧ BulletFree x) ∨ ReadyCut ring root x)
      (by intro x hx; exact Or.inl hx) N U
    exact Nat.le_trans (Nat.le_trans hmono hstrength)
      (firstTwoStagesCost hn ring root N hr.1 hr.2.1 hr.2.2 U)
  have h := Prob.costNumerator_stage_le (nativeE ring) N
    (fun x => Rooted ring root x ∧ BulletFree x) (ReadyCut ring root)
    (2 * n ^ 2) (n ^ 2) hfirst
    (by intro x hx U; exact readinessCost hn ring root x hx.1 hx.2 U) T
  have heq : 2 * n ^ 2 + n ^ 2 = 3 * n ^ 2 := by omega
  rw [heq] at h
  exact h

end ReferencePreparationTrail
end L3

/-!
Doubled finite-horizon stage composition; native return
from the exact absorption cut; and candidate handoff interface.
Every prior byte is unchanged.
-/

namespace L3
namespace ReferencePreparationTrail

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- A doubled finite-horizon stage reserve. Unlike rounding an
n/2 expectation to Nat, the multiplier two remains outside the
actual first-hit counter at every intermediate scheduler cut. -/
private theorem doubledStageReserve {n : Nat} {S : Type}
    (next : S → Fin n → S) (A P : S → Prop) (B : Nat)
    (hcontinuation : ∀ y, A y → ∀ T,
      2 * costNumerator next P y T ≤ n ^ T * B) :
    ∀ y T,
      2 * costNumerator next P y T ≤
        2 * costNumerator next (fun z => A z ∨ P z) y T +
          n ^ T * B := by
  classical
  intro y T
  induction T generalizing y with
  | zero =>
      simp only [costNumerator_zero, Nat.mul_zero, Nat.zero_add]
      exact Nat.zero_le _
  | succ T ih =>
      by_cases hp : P y
      · have hstop : A y ∨ P y := Or.inr hp
        rw [costNumerator_terminal next P y hp (T + 1),
          costNumerator_terminal next (fun z => A z ∨ P z)
            y hstop (T + 1)]
        exact Nat.zero_le _
      · by_cases ha : A y
        · have hstop : A y ∨ P y := Or.inl ha
          rw [costNumerator_terminal next (fun z => A z ∨ P z)
            y hstop (T + 1)]
          simpa only [Nat.mul_zero, Nat.zero_add] using
            hcontinuation y ha (T + 1)
        · have hnot : ¬ (A y ∨ P y) := by
            intro h
            rcases h with hA | hP
            · exact ha hA
            · exact hp hP
          rw [costNumerator_succ next P y hp T,
            costNumerator_succ next (fun z => A z ∨ P z)
              y hnot T]
          have hs :
              (List.ofFn (fun e : Fin n =>
                2 * costNumerator next P (next y e) T)).sum ≤
              (List.ofFn (fun e : Fin n =>
                2 * costNumerator next (fun z => A z ∨ P z)
                  (next y e) T)).sum + n ^ (T + 1) * B := by
            calc
              (List.ofFn (fun e : Fin n =>
                2 * costNumerator next P (next y e) T)).sum ≤
                  (List.ofFn (fun e : Fin n =>
                    2 * costNumerator next (fun z => A z ∨ P z)
                      (next y e) T + n ^ T * B)).sum :=
                ofFn_sum_le _ _ (fun e => ih (next y e))
              _ = (List.ofFn (fun e : Fin n =>
                    2 * costNumerator next (fun z => A z ∨ P z)
                      (next y e) T)).sum + n * (n ^ T * B) := by
                rw [ofFn_sum_add, ofFn_sum_const]
              _ = (List.ofFn (fun e : Fin n =>
                    2 * costNumerator next (fun z => A z ∨ P z)
                      (next y e) T)).sum + n ^ (T + 1) * B := by
                rw [Nat.pow_succ]
                ac_rfl
          have hsum :
              2 * (List.ofFn (fun e : Fin n =>
                costNumerator next P (next y e) T)).sum ≤
              2 * (List.ofFn (fun e : Fin n =>
                costNumerator next (fun z => A z ∨ P z)
                  (next y e) T)).sum + n ^ (T + 1) * B := by
            simpa only [ofFn_sum_mul_left] using hs
          calc
            2 * (n ^ (T + 1) + (List.ofFn (fun e : Fin n =>
                costNumerator next P (next y e) T)).sum) =
              2 * n ^ (T + 1) + 2 * (List.ofFn (fun e : Fin n =>
                costNumerator next P (next y e) T)).sum := by
                  rw [Nat.mul_add]
            _ ≤ 2 * n ^ (T + 1) +
                (2 * (List.ofFn (fun e : Fin n =>
                  costNumerator next (fun z => A z ∨ P z)
                    (next y e) T)).sum + n ^ (T + 1) * B) :=
              Nat.add_le_add_left hsum _
            _ = 2 * (n ^ (T + 1) + (List.ofFn (fun e : Fin n =>
                  costNumerator next (fun z => A z ∨ P z)
                    (next y e) T)).sum) + n ^ (T + 1) * B := by
              omega

/-- Two-stage composition with an exact half-step charge. -/
theorem doubledStageCost {n : Nat} {S : Type}
    (next : S → Fin n → S) (x : S)
    (A P : S → Prop) (B C : Nat)
    (hfirst : ∀ T,
      2 * costNumerator next (fun z => A z ∨ P z) x T ≤
        n ^ T * B)
    (hsecond : ∀ y, A y → ∀ T,
      2 * costNumerator next P y T ≤ n ^ T * C) :
    ∀ T, 2 * costNumerator next P x T ≤
      n ^ T * (B + C) := by
  intro T
  calc
    2 * costNumerator next P x T ≤
        2 * costNumerator next (fun z => A z ∨ P z) x T +
          n ^ T * C :=
      doubledStageReserve next A P C hsecond x T
    _ ≤ n ^ T * B + n ^ T * C :=
      Nat.add_le_add_right (hfirst T) _
    _ = n ^ T * (B + C) := by rw [Nat.mul_add]

private theorem twiceSquare (n T : Nat) (a : Nat) :
    2 * (n ^ T * (a * n ^ 2)) =
      n ^ T * ((2 * a) * n ^ 2) := by
  ac_rfl

/-- Exact doubled budget for the first ready-cut, followed by the
first genuine leader-incident firing. -/
theorem firstFreshDoubledCost {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n)
    (hroot : Rooted ring root N) (T : Nat) :
    2 * costNumerator (nativeE ring) (FiredCut ring root) N T ≤
      n ^ T * (6 * n ^ 2 + n) := by
  have hfirst : ∀ U,
      2 * costNumerator (nativeE ring)
        (fun x => ReadyCut ring root x ∨ FiredCut ring root x)
        N U ≤ n ^ U * (6 * n ^ 2) := by
    intro U
    have hmono := Prob.costNumerator_target_mono (nativeE ring)
      (ReadyCut ring root)
      (fun x => ReadyCut ring root x ∨ FiredCut ring root x)
      (by intro x hx; exact Or.inl hx) N U
    have hc := firstThreeStagesCost hn ring root N hroot U
    calc
      2 * costNumerator (nativeE ring)
          (fun x => ReadyCut ring root x ∨ FiredCut ring root x)
          N U ≤
        2 * costNumerator (nativeE ring) (ReadyCut ring root)
          N U := Nat.mul_le_mul_left 2 hmono
      _ ≤ 2 * (n ^ U * (3 * n ^ 2)) :=
        Nat.mul_le_mul_left 2 hc
      _ = n ^ U * (6 * n ^ 2) := by
        calc
          _ = n ^ U * (2 * (3 * n ^ 2)) := by ac_rfl
          _ = n ^ U * (6 * n ^ 2) := by
            congr 1
            omega
  exact doubledStageCost (nativeE ring) N
    (ReadyCut ring root) (FiredCut ring root)
    (6 * n ^ 2) n hfirst
    (by intro z hz U; exact freshHalfCost hn ring root z hz U) T

/-- Four n² stages plus the genuine n/2 incident clock, without
rounding the latter. The stopping predicate is the exact
post-absorption native signal word, not just an empty bullet field. -/
theorem firstAbsorptionDoubledCost {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n)
    (hroot : Rooted ring root N) (T : Nat) :
    2 * costNumerator (nativeE ring) (AbsorbedCut ring root)
      N T ≤ n ^ T * (8 * n ^ 2 + n) := by
  have hfirst : ∀ U,
      2 * costNumerator (nativeE ring)
        (fun x => FiredCut ring root x ∨ AbsorbedCut ring root x)
        N U ≤ n ^ U * (6 * n ^ 2 + n) := by
    intro U
    exact Nat.le_trans
      (Nat.mul_le_mul_left 2
        (Prob.costNumerator_target_mono (nativeE ring)
          (FiredCut ring root)
          (fun x => FiredCut ring root x ∨ AbsorbedCut ring root x)
          (by intro x hx; exact Or.inl hx) N U))
      (firstFreshDoubledCost hn ring root N hroot U)
  have hsecond : ∀ z, FiredCut ring root z → ∀ U,
      2 * costNumerator (nativeE ring)
        (AbsorbedCut ring root) z U ≤ n ^ U * (2 * n ^ 2) := by
    intro z hz U
    have hc := circulationCost hn ring root z hz U
    calc
      2 * costNumerator (nativeE ring)
          (AbsorbedCut ring root) z U ≤
        2 * (n ^ U * n ^ 2) :=
        Nat.mul_le_mul_left 2 hc
      _ = n ^ U * (2 * n ^ 2) := by ac_rfl
  have h := doubledStageCost (nativeE ring) N
    (FiredCut ring root) (AbsorbedCut ring root)
    (6 * n ^ 2 + n) (2 * n ^ 2) hfirst hsecond T
  exact Nat.le_trans h
    (Nat.mul_le_mul_left (n ^ T) (by omega :
      6 * n ^ 2 + n + 2 * n ^ 2 ≤ 8 * n ^ 2 + n))

/-- The clockwise followers with true signal form a suffix,
including the last site. Root signal is deliberately separate. -/
def ReturnSuffix {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n) : Prop :=
  (N (PPL.shiftRight ring root (n - 1))).sg = true ∧
  ∀ k : Nat, 1 ≤ k → k + 1 < n →
    (N (PPL.shiftRight ring root k)).sg = true →
      (N (PPL.shiftRight ring root (k + 1))).sg = true

/-- Suffix order is inherited along a clockwise chain. -/
theorem returnSuffixAll {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n)
    (hs : ReturnSuffix ring root N)
    (hone : (N (PPL.shiftRight ring root 1)).sg = true) :
    ∀ k : Nat, 1 ≤ k → k < n →
      (N (PPL.shiftRight ring root k)).sg = true := by
  intro k
  induction k with
  | zero =>
      intro hk _
      exact False.elim (by omega : False)
  | succ k ih =>
      intro hk hkn
      by_cases hkzero : k = 0
      · have hindex : k + 1 = 1 := by omega
        rw [hindex]
        exact hone
      · have hprev := ih (by omega : 1 ≤ k) (by omega : k < n)
        have hnext := hs.2 k (by omega) hkn hprev
        exact hnext

/-- Native stopping invariant on the signal return. The last
conjunct is a historical fact: the FIRST ready root must be
accompanied by all follower signals one. It is not implied by an
arbitrary Cartesian ready-and-bullet-free singleton. -/
def ReturnGood {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n) : Prop :=
  Rooted ring root N ∧ BulletFree N ∧ ReturnSuffix ring root N ∧
  ((N root).sg = true → ∀ i : Fin n, (N i).sg = true)

/-- The exact absorption cut initializes the return-wave invariant.
The root is still quiet and no filler signals have been assumed. -/
theorem absorbedReturnGood {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n)
    (h : AbsorbedCut ring root N) :
    ReturnGood ring root N := by
  have hz : (N root).sg = false := by
    have hh := h.2.2.2 0 (by omega : 0 < n - 1)
    rw [referencePreparationShiftZero] at hh
    exact hh
  refine ⟨h.1, h.2.1, ⟨h.2.2.1, ?_⟩, ?_⟩
  · intro k hk hkn hs
    have hf := h.2.2.2 k (by omega : k < n - 1)
    rw [hf] at hs
    cases hs
  · intro hready
    rw [hz] at hready
    cases hready

/-- A native return cut with a ready root is actually the all-one,
bullet-free native preparation target, not merely ReadyCut. -/
theorem returnPreparedIfReady {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n)
    (hgood : ReturnGood ring root N)
    (hready : (N root).sg = true) :
    ReferencePreparationNativePreparedAt root N := by
  refine ⟨hgood.1.1, hgood.1.2.1, ?_⟩
  intro i
  exact ⟨hgood.2.1 i, hgood.2.2.2 hready i⟩

/-- At a nonterminal return cut all leaders are quiet; no edge
can fire before root readiness. -/
private theorem returnNotPreparedQuiet {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n)
    (hgood : ReturnGood ring root N)
    (hnot : ¬ ReferencePreparationNativePreparedAt root N) :
    (N root).sg = false := by
  cases hs : (N root).sg with
  | false => rfl
  | true =>
      exact False.elim (hnot
        (returnPreparedIfReady ring root N hgood hs))

/-- The only way a quiet bullet-free root can first become ready
is by its own outgoing service, whose old follower already had
signal one. An incoming edge cannot turn the responder root ready. -/
private theorem returnRootNewFromFollower {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n) (e : Fin n)
    (hr : Rooted ring root N) (hb : BulletFree N)
    (hz : (N root).sg = false)
    (hnew : (nativeE ring N e root).sg = true) :
    (N (PPL.shiftRight ring root 1)).sg = true := by
  have hq := noFire N root hr.2.1 hz
  have hpair := sealed_prep_actual_old_pair ring N e (rightNe hn ring e)
  have hrow := emptyQuietPair (N e) (N (ring.rightNeighbor e))
    (hb e) (hb (ring.rightNeighbor e)) (hq e)
    (hq (ring.rightNeighbor e))
  by_cases he : e = root
  · have hfollow : (N (ring.rightNeighbor root)).l = false := by
      apply follower N root (ring.rightNeighbor root) hr.2.1
      exact rightNe hn ring root
    have hformula := (emptyQuietStep hn ring N e hb
      (hq e) (hq (ring.rightNeighbor e))).2.2
    have hready : ((N root).sg || (N (ring.rightNeighbor root)).sg ||
        (N (ring.rightNeighbor root)).l) = true := by
      rw [he] at hformula hnew
      exact hformula.symm.trans hnew
    have hneighbor : (N (ring.rightNeighbor root)).sg = true := by
      cases hs : (N (ring.rightNeighbor root)).sg with
      | true => rfl
      | false =>
          rw [hz, hs, hfollow] at hready
          cases hready
    rw [shiftOne]
    exact hneighbor
  · by_cases hj : root = ring.rightNeighbor e
    · have hs : (nativeE ring N e root).sg =
          (N root).sg := by
        calc
          (nativeE ring N e root).sg =
              (certLiteralEPair (N e)
                (N (ring.rightNeighbor e))).2.sg := by
                  rw [hj]
                  exact congrArg CertNative.sg hpair.2
          _ = (N (ring.rightNeighbor e)).sg := hrow.2.2.2
          _ = (N root).sg := by rw [← hj]
      rw [hs, hz] at hnew
      cases hnew
    · have hf := frame ring N e root (Ne.symm he) hj
      rw [hf, hz] at hnew
      cases hnew

/-- Before root readiness, a full clockwise suffix of one-signals
cannot acquire a gap. The source may become one only if its old
right follower already had a one, and every true signal is monotone. -/
theorem returnSuffixStep {n : Nat} (hn : 5 ≤ n)
    (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n) (e : Fin n)
    (hr : Rooted ring root N) (hb : BulletFree N)
    (hz : (N root).sg = false)
    (hsuffix : ReturnSuffix ring root N) :
    ReturnSuffix ring root (nativeE ring N e) := by
  have hq := noFire N root hr.2.1 hz
  have hs := emptyQuietStep hn ring N e hb
    (hq e) (hq (ring.rightNeighbor e))
  have hpair := sealed_prep_actual_old_pair ring N e (rightNe hn ring e)
  have hrow := emptyQuietPair (N e) (N (ring.rightNeighbor e))
    (hb e) (hb (ring.rightNeighbor e)) (hq e)
    (hq (ring.rightNeighbor e))
  refine ⟨hs.2.1 _ hsuffix.1, ?_⟩
  intro k hk hkn hpost
  by_cases he : PPL.shiftRight ring root k = e
  · have hj : ring.rightNeighbor e =
        PPL.shiftRight ring root (k + 1) := by
      calc
        ring.rightNeighbor e =
            ring.rightNeighbor (PPL.shiftRight ring root k) := by rw [he]
        _ = PPL.shiftRight ring root (k + 1) :=
          (referencePreparationShiftSucc ring root k).symm
    have hyl : (N (ring.rightNeighbor e)).l = false := by
      apply follower N root _ hr.2.1
      rw [hj]
      exact referencePreparation_sealed_site_ne
        ring root (k + 1) (by omega) hkn
    have hnew :
        ((N e).sg || (N (ring.rightNeighbor e)).sg ||
          (N (ring.rightNeighbor e)).l) = true := by
      rw [he] at hpost
      exact hs.2.2.symm.trans hpost
    have hold : (N (ring.rightNeighbor e)).sg = true := by
      cases hx : (N e).sg with
      | true =>
          have hsource : (N (PPL.shiftRight ring root k)).sg = true := by
            rw [he]
            exact hx
          have hy := hsuffix.2 k hk hkn hsource
          rw [← hj] at hy
          exact hy
      | false =>
          cases hy : (N (ring.rightNeighbor e)).sg with
          | true => rfl
          | false =>
              rw [hx, hy, hyl] at hnew
              cases hnew
    have hrnext : (N (PPL.shiftRight ring root (k + 1))).sg = true := by
      rw [← hj]
      exact hold
    exact hs.2.1 _ hrnext
  · by_cases hres :
        PPL.shiftRight ring root k = ring.rightNeighbor e
    · have hold : (N (PPL.shiftRight ring root k)).sg = true := by
        rw [hres, hpair.2, hrow.2.2.2] at hpost
        rw [hres]
        exact hpost
      exact hs.2.1 _ (hsuffix.2 k hk hkn hold)
    · rw [frame ring N e (PPL.shiftRight ring root k)
          he hres] at hpost
      exact hs.2.1 _ (hsuffix.2 k hk hkn hpost)

/-- The return suffix is preserved on every real nativeE edge
before the native all-one target, including the first ready edge. -/
theorem returnGoodStep {n : Nat} (hn : 5 ≤ n)
    (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n) (e : Fin n)
    (hgood : ReturnGood ring root N)
    (hz : (N root).sg = false) :
    ReturnGood ring root (nativeE ring N e) := by
  have hquiet := beforeReadyStep hn ring root N e
    hgood.1 hgood.2.1 hz
  have hword := returnSuffixStep hn ring root N e
    hgood.1 hgood.2.1 hz hgood.2.2.1
  refine ⟨rootedStep hn ring root N e hgood.1,
    hquiet.2.1, hword, ?_⟩
  intro hready i
  have hfront := returnRootNewFromFollower hn ring root N e
    hgood.1 hgood.2.1 hz hready
  obtain ⟨k, hk, hsite⟩ :=
    referencePreparationShiftSurj ring root i
  by_cases hkzero : k = 0
  · have hi : i = root := by
      calc
        i = PPL.shiftRight ring root k := hsite.symm
        _ = PPL.shiftRight ring root 0 := by rw [hkzero]
        _ = root := referencePreparationShiftZero ring root
    rw [hi]
    exact hready
  · have hold : (N (PPL.shiftRight ring root k)).sg = true :=
      returnSuffixAll ring root N hgood.2.2.1 hfront k
        (by omega) hk
    have hnew := hquiet.2.2 (PPL.shiftRight ring root k) hold
    rw [← hsite]
    exact hnew

/-- Cost of the complete native all-signals-one return from the
specific post-absorption suffix. The cursor is the same backward
nominated-edge clock used for first readiness. -/
theorem returnCostLeClock {n : Nat} (hn : 5 ≤ n)
    (ring : DirectedRing n) (root : Fin n) :
    ∀ T (z : TripleNativeState n × Nat),
      ReadinessGood ring root z →
      ReturnGood ring root z.1 →
      costNumerator (nativeE ring)
        (ReferencePreparationNativePreparedAt root) z.1 T ≤
      costNumerator (readinessStep ring root)
        ReadinessDone z T := by
  classical
  intro T
  induction T with
  | zero =>
      intro z _ _
      simp only [costNumerator_zero]
      exact Nat.le_refl 0
  | succ T ih =>
      intro z hr hg
      by_cases hp : ReferencePreparationNativePreparedAt root z.1
      · rw [costNumerator_terminal (nativeE ring)
          (ReferencePreparationNativePreparedAt root) z.1 hp (T + 1)]
        exact Nat.zero_le _
      · have hz := returnNotPreparedQuiet ring root z.1 hg hp
        have hnotready : ¬ ReadyCut ring root z.1 := by
          intro hready
          exact hp (returnPreparedIfReady ring root z.1 hg hready.2.2)
        have hd : ¬ ReadinessDone z := by
          intro hdone
          exact hnotready (readinessDoneReady ring root z hr hdone)
        rw [costNumerator_succ (nativeE ring)
          (ReferencePreparationNativePreparedAt root) z.1 hp T,
          costNumerator_succ (readinessStep ring root)
            ReadinessDone z hd T]
        exact Nat.add_le_add_left
          (ofFn_sum_le
            (fun e : Fin n =>
              costNumerator (nativeE ring)
                (ReferencePreparationNativePreparedAt root)
                (nativeE ring z.1 e) T)
            (fun e : Fin n =>
              costNumerator (readinessStep ring root)
                ReadinessDone (readinessStep ring root z e) T)
            (fun e =>
              ih (readinessStep ring root z e)
                (readinessGoodStep hn ring root z e hr hnotready)
                (returnGoodStep hn ring root z.1 e hg hz))) _

/-- Native analogue of the final signal-return stage. No candidate
record statement is implicit in this native-only theorem. -/
theorem absorptionReturnCost {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n)
    (h : AbsorbedCut ring root N) (T : Nat) :
    costNumerator (nativeE ring)
      (ReferencePreparationNativePreparedAt root) N T ≤
      n ^ T * n ^ 2 := by
  have hr : ReadinessGood ring root (N, n) := by
    refine ⟨h.1, h.2.1, Nat.le_refl n, ?_⟩
    intro k hk hkn
    change n ≤ k at hk
    omega
  have hg := absorbedReturnGood hn ring root N h
  have hc := returnCostLeClock hn ring root T (N, n) hr hg
  have hd := readinessClockCost ring root (N, n) T
  have hs := Nat.le_trans hc hd
  simpa only [Nat.pow_two] using hs

/-- Exact doubled H.1 native bound (five n² stages plus the
unrounded n/2 incident stage). The target is native-only; it
does not imply candidate retirement or inherited-authority
extinction on a physical headline configuration. -/
theorem nativeSingletonPreparationDoubledCost {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n)
    (hroot : Rooted ring root N) (T : Nat) :
    2 * costNumerator (nativeE ring)
      (ReferencePreparationNativePreparedAt root) N T ≤
      n ^ T * (10 * n ^ 2 + n) := by
  have hfirst : ∀ U,
      2 * costNumerator (nativeE ring)
        (fun x => AbsorbedCut ring root x ∨
          ReferencePreparationNativePreparedAt root x)
        N U ≤ n ^ U * (8 * n ^ 2 + n) := by
    intro U
    exact Nat.le_trans
      (Nat.mul_le_mul_left 2
        (Prob.costNumerator_target_mono (nativeE ring)
          (AbsorbedCut ring root)
          (fun x => AbsorbedCut ring root x ∨
            ReferencePreparationNativePreparedAt root x)
          (by intro x hx; exact Or.inl hx) N U))
      (firstAbsorptionDoubledCost hn ring root N hroot U)
  have hsecond : ∀ z, AbsorbedCut ring root z → ∀ U,
      2 * costNumerator (nativeE ring)
        (ReferencePreparationNativePreparedAt root) z U ≤
          n ^ U * (2 * n ^ 2) := by
    intro z hz U
    have hc := absorptionReturnCost hn ring root z hz U
    calc
      2 * costNumerator (nativeE ring)
          (ReferencePreparationNativePreparedAt root) z U ≤
        2 * (n ^ U * n ^ 2) :=
        Nat.mul_le_mul_left 2 hc
      _ = n ^ U * (2 * n ^ 2) := by ac_rfl
  have hs := doubledStageCost (nativeE ring) N
    (AbsorbedCut ring root)
    (ReferencePreparationNativePreparedAt root)
    (8 * n ^ 2 + n) (2 * n ^ 2) hfirst hsecond T
  exact Nat.le_trans hs
    (Nat.mul_le_mul_left (n ^ T) (by omega :
      8 * n ^ 2 + n + 2 * n ^ 2 ≤ 10 * n ^ 2 + n))

/-- Precise physical candidate handoff interface. A nativeE-only
history cannot control candidate fields of HeadlineConfiguration.
The additional premise below is the actual candidate-zero condition
on the same physical cut, not an inference from the native bound. -/
theorem nativePreparedPhysicalCandidateHandoff {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : HeadlineConfiguration n)
    (hnative : ReferencePreparationNativePreparedAt
      root (nativeProjection C))
    (hprotected : Protected ring (nativeProjection C))
    (hgrant : NativeLiftGrantFree C)
    (hclean : C_native ring (nativeProjection C))
    (hcand : EmptyCandidates (fun i => NativeCand.ofAgent (C i))) :
    ReferencePreparationPreparedCore ring C := by
  refine ⟨hprotected, hgrant, ?_, hclean, ?_, hcand⟩
  · exact ⟨root, hnative.1, hnative.2.1⟩
  · intro i
    exact hnative.2.2 i

end ReferencePreparationTrail
end L3

/-!
Exact no-FIRE candidate projection on the *physical* history.

This deliberately distinguishes
the first native-prepared hit from the later fresh-circulation cut of H.1.
The latter has not yet been given a candidate-retirement cost proof.
-/

namespace L3
namespace ReferencePreparationCandidate

set_option autoImplicit false
set_option Elab.async false

/-- Only the existing native and candidate coordinates of the actual
headline configuration; no additional physical protocol fields. -/
def physicalCandidates {n : Nat}
    (C : HeadlineConfiguration n) : Fin n → NativeCand :=
  fun i => NativeCand.ofAgent (C i)

/-- The exact birth-disabled map Phi_e iterated on the same scheduler
word. This is a projection of the existing owner, not a new protocol. -/
def candidateWord {n : Nat} (ring : DirectedRing n) :
    (Fin n → NativeCand) → List (Fin n) → (Fin n → NativeCand)
  | S, [] => S
  | S, e :: es =>
      candidateWord ring (birthFreeCandidateStep ring S e) es

/-- The literal full physical transition projects to Phi_e whenever
the OLD FIRE selection is none. In particular unrelated certificate,
H/K and token owners cannot alter these coordinates. -/
theorem noFirePhysicalStep {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (hf : NativeLiftNoFireOn ring C e) :
    physicalCandidates (headlinePhysicalNext ring C e) =
      birthFreeCandidateStep ring (physicalCandidates C) e := by
  have hfire :
      oldFire (C e) (C (ring.rightNeighbor e)) = none := hf
  have hp := transitionCandidate_noFire
    (compileAdvice (ceilLogTwo n))
    (C e) (C (ring.rightNeighbor e)) hfire
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring (by omega : 2 ≤ n) e
  have hsource :
      (physicalCandidates (headlinePhysicalNext ring C e)) e =
        (birthFreeCandidatePair
          (physicalCandidates C e)
          (physicalCandidates C (ring.rightNeighbor e))).1 :=
    (congrArg NativeCand.ofAgent
      (headlineRendezvousStepAtSource ring C e)).trans
      (congrArg Prod.fst hp)
  have htarget :
      (physicalCandidates (headlinePhysicalNext ring C e))
          (ring.rightNeighbor e) =
        (birthFreeCandidatePair
          (physicalCandidates C e)
          (physicalCandidates C (ring.rightNeighbor e))).2 :=
    (congrArg NativeCand.ofAgent
      (headlineRendezvousStepAtResponder ring
        (by omega : 2 ≤ n) C e)).trans
      (congrArg Prod.snd hp)
  funext i
  by_cases he : i = e
  · subst i
    have hright :
        birthFreeCandidateStep ring (physicalCandidates C) e e =
          (birthFreeCandidatePair
            (physicalCandidates C e)
            (physicalCandidates C (ring.rightNeighbor e))).1 := by
      simp [birthFreeCandidateStep]
    exact hsource.trans hright.symm
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      have hright :
          birthFreeCandidateStep ring (physicalCandidates C)
              e (ring.rightNeighbor e) =
            (birthFreeCandidatePair
              (physicalCandidates C e)
              (physicalCandidates C (ring.rightNeighbor e))).2 := by
        simp [birthFreeCandidateStep, hne]
      exact htarget.trans hright.symm
    · have hframe :
          (physicalCandidates (headlinePhysicalNext ring C e)) i =
            (physicalCandidates C) i :=
        congrArg NativeCand.ofAgent
          (headlineRendezvousStepAway ring C e i he hj)
      have hright :
          birthFreeCandidateStep ring (physicalCandidates C) e i =
            (physicalCandidates C) i := by
        simp [birthFreeCandidateStep, he, hj]
      exact hframe.trans hright.symm

/-- Projection commutes with EVERY prefix of an actually revealed
birth-free word, not merely with the nominated edge sequence. -/
theorem noFirePhysicalWord {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (edges : List (Fin n))
    (hword : NativeLiftNoFireWord ring C edges) :
    physicalCandidates (nativeLiftRealRun ring C edges) =
      candidateWord ring (physicalCandidates C) edges := by
  induction edges generalizing C with
  | nil =>
      rfl
  | cons e es ih =>
      have hs := noFirePhysicalStep hn ring C e hword.1
      have ht := ih (headlinePhysicalNext ring C e) hword.2
      change physicalCandidates
          (nativeLiftRealRun ring (headlinePhysicalNext ring C e) es) =
        candidateWord ring
          (birthFreeCandidateStep ring (physicalCandidates C) e) es
      rw [hs] at ht
      exact ht

/-- The generated H_cand witness extends along the same actual
no-FIRE scheduler word, using CandidateClosure rather than copying
or rebuilding its ghost definition. -/
theorem noFirePhysicalHistory {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (edges : List (Fin n))
    (hword : NativeLiftNoFireWord ring C edges)
    (horigin : H_cand ring (physicalCandidates C)) :
    H_cand ring
      (physicalCandidates (nativeLiftRealRun ring C edges)) := by
  induction edges generalizing C with
  | nil =>
      exact horigin
  | cons e es ih =>
      have hstep : H_cand ring
          (birthFreeCandidateStep ring (physicalCandidates C) e) :=
        H_cand_birthFree_step ring (physicalCandidates C) e horigin
      have hp := noFirePhysicalStep hn ring C e hword.1
      rw [← hp] at hstep
      exact ih (headlinePhysicalNext ring C e) hword.2 hstep

/-- A zero candidate origin remains zero along the abstract Phi word.
This deliberately does NOT assert that arbitrary nonzero origins retire. -/
theorem candidateWordEmpty {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (S : Fin n → NativeCand) (edges : List (Fin n))
    (hzero : EmptyCandidates S) :
    EmptyCandidates (candidateWord ring S edges) := by
  induction edges generalizing S with
  | nil =>
      exact hzero
  | cons e es ih =>
      exact ih (birthFreeCandidateStep ring S e)
        (EmptyCandidates_step ring hn S e hzero)

/-- A genuine full-protocol zero-origin consequence. -/
theorem noFirePhysicalWordEmpty {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (edges : List (Fin n))
    (hword : NativeLiftNoFireWord ring C edges)
    (hzero : EmptyCandidates (physicalCandidates C)) :
    EmptyCandidates
      (physicalCandidates (nativeLiftRealRun ring C edges)) := by
  have h := candidateWordEmpty (by omega : 2 ≤ n) ring
    (physicalCandidates C) edges hzero
  have hp := noFirePhysicalWord hn ring C edges hword
  rw [← hp] at h
  exact h

/-- Exact SAN erasure, including an unoccupied OLD candidate. -/
theorem postLeaderErases (old : NativeCand)
    (postE : CertNative) (enter : Bool)
    (hl : postE.l = true) :
    nativeCandNext old postE enter = zeroCandidate := by
  cases hc : old.candidate.C <;>
    simp [nativeCandNext, nativeCandSelect, nativeCandPrivate,
      zeroCandidate, hc, hl]

/-- Exact K2 erasure on the first returning signal when the resident
candidate has received its first entry. -/
theorem returningSignalErases (old : NativeCand)
    (postE : CertNative) (enter : Bool)
    (hc : old.candidate.C = true)
    (ha : old.candidate.alpha = true)
    (hl : postE.l = false)
    (hb : postE.b = (0 : Fin 3))
    (hs : postE.sg = true) :
    nativeCandNext old postE enter = zeroCandidate := by
  simp [nativeCandNext, nativeCandSelect, nativeCandPrivate,
    zeroCandidate, hc, ha, hl, hb, hs]

/-- A mature resident with an empty post-elimination bullet is
eliminated, by K2 if returning and armed, otherwise by PROM. -/
theorem matureExitErases (old : NativeCand)
    (postE : CertNative) (enter : Bool)
    (hc : old.candidate.C = true)
    (hm : old.candidate.m = true)
    (hl : postE.l = false)
    (hb : postE.b = (0 : Fin 3)) :
    nativeCandNext old postE enter = zeroCandidate := by
  cases ha : old.candidate.alpha <;>
    cases hs : postE.sg <;>
      simp [nativeCandNext, nativeCandSelect, nativeCandPrivate,
        zeroCandidate, hc, hm, hl, hb, ha, hs]

/-- A first live-bullet entry into an unarmed occupied follower
supplies first credit. This only checks the literal local owner. -/
theorem freshLiveEntryArms (old : NativeCand)
    (postE : CertNative)
    (hc : old.candidate.C = true)
    (ha : old.candidate.alpha = false)
    (hl : postE.l = false)
    (hb : postE.b = (2 : Fin 3))
    (hs : postE.sg = false) :
    (nativeCandNext old postE true).alpha = true := by
  simp [nativeCandNext, nativeCandSelect, nativeCandPrivate,
    zeroCandidate, hc, ha, hl, hb, hs]

/-- Restricted handoff: the candidate-zero assumption is moved to
a genuine earlier physical origin and transported by the exact
no-FIRE word. It does NOT handle the arbitrary-credit H.1 origin. -/
theorem handoffFromEmptyOrigin {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n) (root : Fin n)
    (C : HeadlineConfiguration n) (edges : List (Fin n))
    (hword : NativeLiftNoFireWord ring C edges)
    (hzero : EmptyCandidates (physicalCandidates C))
    (hnative : ReferencePreparationNativePreparedAt root
      (nativeProjection (nativeLiftRealRun ring C edges)))
    (hprotected : Protected ring
      (nativeProjection (nativeLiftRealRun ring C edges)))
    (hgrant : NativeLiftGrantFree (nativeLiftRealRun ring C edges))
    (hclean : C_native ring
      (nativeProjection (nativeLiftRealRun ring C edges))) :
    ReferencePreparationPreparedCore ring
      (nativeLiftRealRun ring C edges) := by
  exact ReferencePreparationTrail.nativePreparedPhysicalCandidateHandoff
    ring root (nativeLiftRealRun ring C edges)
    hnative hprotected hgrant hclean
    (noFirePhysicalWordEmpty hn ring C edges hword hzero)

/-- Arithmetic ledger only: if an independently proved extra fresh
circulation/return costs at most 2n^2+n/2, then its doubled
contribution is 4n^2+n and the total ledger is 14n^2+2n.
This arithmetic identity is NOT an expected-time certificate. -/
theorem additionalCirculationDoubledLedger (n : Nat) :
    (10 * n ^ 2 + n) + (4 * n ^ 2 + n) =
      14 * n ^ 2 + 2 * n := by
  omega

/-! A literal physical counterexample to candidate retirement at the
FIRST native-prepared hit.  All unrelated Agent fields come from the
legal blank agent. No role or candidate state is fabricated in Phi_e. -/

private def counterRing : DirectedRing 5 := ⟨by decide⟩

private def counterPhysical : HeadlineConfiguration 5 :=
  fun i =>
    { Agent.blank (compileAdvice (ceilLogTwo 5)) with
      l := (i.val == 0)
      sh := (i.val == 0)
      sg := !(i.val == 0)
      C := (i.val == 2) }

/-- Every old physical grant is false. -/
theorem counterGrantFree : NativeLiftGrantFree counterPhysical := by
  intro i
  rfl

/-- Consequently the one-edge witness has no selected birth. -/
theorem counterNoFire :
    NativeLiftNoFireOn counterRing counterPhysical (0 : Fin 5) := by
  exact (native_lift_no_fire_cut_of_grant_free
    counterRing counterPhysical counterGrantFree) (0 : Fin 5)

/-- The starting native state is a protected singleton. -/
theorem counterRooted :
    ReferencePreparationTrail.Rooted counterRing (0 : Fin 5)
      (nativeProjection counterPhysical) := by
  unfold ReferencePreparationTrail.Rooted
  decide +kernel

/-- The initial root signal is zero: this is not a time-zero
native-prepared target. -/
theorem counterNotPrepared :
    ¬ ReferencePreparationNativePreparedAt (0 : Fin 5)
        (nativeProjection counterPhysical) := by
  intro h
  have hs := (h.2.2 (0 : Fin 5)).2
  change false = true at hs
  cases hs

/-- Service of 0 -> 1 first makes the root signal one, without any
bullet. The exact physical native projection is the E output. -/
theorem counterPreparedAfterEdge :
    ReferencePreparationNativePreparedAt (0 : Fin 5)
      (nativeProjection
        (headlinePhysicalNext counterRing counterPhysical (0 : Fin 5))) := by
  have hp := native_lift_no_fire_step (by decide : 3 ≤ 5)
    counterRing counterPhysical (0 : Fin 5) counterNoFire
  have htarget :
      ReferencePreparationNativePreparedAt (0 : Fin 5)
        (nativeE counterRing
          (nativeProjection counterPhysical) (0 : Fin 5)) := by
    unfold ReferencePreparationNativePreparedAt
    decide +kernel
  rw [← hp] at htarget
  exact htarget

/-- The untouched follower 2 still carries (1,0,0). -/
theorem counterCandidateAtTwo :
    (physicalCandidates
      (headlinePhysicalNext counterRing counterPhysical (0 : Fin 5))
      (2 : Fin 5)).candidate =
      { C := true, alpha := false, m := false } := by
  have hp := noFirePhysicalStep (by decide : 5 ≤ 5)
    counterRing counterPhysical (0 : Fin 5) counterNoFire
  have htarget :
      (birthFreeCandidateStep counterRing
        (physicalCandidates counterPhysical) (0 : Fin 5)
        (2 : Fin 5)).candidate =
        { C := true, alpha := false, m := false } := by
    decide +kernel
  rw [← hp] at htarget
  exact htarget

/-- Nonempty candidate at the first native-prepared cut. -/
theorem counterNotEmptyAfterEdge :
    ¬ EmptyCandidates
      (physicalCandidates
        (headlinePhysicalNext counterRing counterPhysical (0 : Fin 5))) := by
  intro h
  have hs := h (2 : Fin 5)
  have hn :
      ({ C := true, alpha := false, m := false } : CPriv) ≠
        zeroCandidate := by
    decide
  exact hn (counterCandidateAtTwo.symm.trans hs)

/-- A single physical service is a non-vacuous counterexample:
Rooted start, nonterminal native start, no-FIRE edge, native target,
yet nonzero candidate. The scheduler word is [(0 : Fin 5)]. -/
theorem firstNativePreparedDoesNotRetireCandidates :
    ReferencePreparationTrail.Rooted counterRing (0 : Fin 5)
        (nativeProjection counterPhysical) ∧
    ¬ ReferencePreparationNativePreparedAt (0 : Fin 5)
        (nativeProjection counterPhysical) ∧
    NativeLiftNoFireOn counterRing counterPhysical (0 : Fin 5) ∧
    ReferencePreparationNativePreparedAt (0 : Fin 5)
      (nativeProjection
        (headlinePhysicalNext counterRing counterPhysical (0 : Fin 5))) ∧
    ¬ EmptyCandidates
      (physicalCandidates
        (headlinePhysicalNext counterRing counterPhysical (0 : Fin 5))) :=
  ⟨counterRooted, counterNotPrepared, counterNoFire,
    counterPreparedAfterEdge, counterNotEmptyAfterEdge⟩

end ReferencePreparationCandidate
end L3

/-!
Candidate return after a distinguished circulation.

The finite-horizon return-stage
certificate below starts at an AbsorbedCut WITH the explicit
candidate sweep invariant. Establishing that invariant from an
arbitrary candidate record on the preceding fresh circulation
remains open. No theorem silently promotes the first native
prepared hit to an EmptyCandidates cut.
-/

namespace L3
namespace ReferencePreparationCandidate

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The selected owner cannot create occupancy from an unoccupied
candidate, even if its inactive alpha/m scratch was arbitrary. -/
theorem candidateNoResurrection (old : NativeCand)
    (postE : CertNative) (enter : Bool)
    (h : old.candidate.C = false) :
    nativeCandNext old postE enter = zeroCandidate := by
  simp [nativeCandNext, nativeCandSelect, nativeCandPrivate,
    zeroCandidate, h]

/-- At either live or dummy entry, any occupied follower obtains
first credit; its old mature credit need not be zero. The entry must
actually be selected and the post-E signal must be zero. -/
theorem candidateArrivalArms (old : NativeCand)
    (postE : CertNative)
    (hc : old.candidate.C = true)
    (hl : postE.l = false)
    (hs : postE.sg = false)
    (hb : postE.b = (1 : Fin 3) ∨ postE.b = (2 : Fin 3)) :
    (nativeCandNext old postE true).C = true ∧
      (nativeCandNext old postE true).alpha = true := by
  rcases hb with hb | hb
  · cases ha : old.candidate.alpha with
    | false =>
        simp [nativeCandNext, nativeCandSelect, nativeCandPrivate,
          hc, ha, hl, hs, hb]
    | true =>
        simp [nativeCandNext, nativeCandSelect, nativeCandPrivate,
          hc, ha, hl, hs, hb]
  · cases ha : old.candidate.alpha with
    | false =>
        simp [nativeCandNext, nativeCandSelect, nativeCandPrivate,
          hc, ha, hl, hs, hb]
    | true =>
        simp [nativeCandNext, nativeCandSelect, nativeCandPrivate,
          hc, ha, hl, hs, hb]

/-- When an armed candidate's bullet leaves its host, mature credit
causes PROM erasure, a returning one-signal causes K2 erasure, and
the only remaining occupied case is armed, immature and signal-zero.
This includes both live and dummy bullets. -/
theorem candidateBulletExit (old : NativeCand)
    (postE : CertNative)
    (hc : old.candidate.C = true)
    (ha : old.candidate.alpha = true)
    (hl : postE.l = false)
    (hb : postE.b = (0 : Fin 3)) :
    nativeCandNext old postE false = zeroCandidate ∨
      ((nativeCandNext old postE false).C = true ∧
       (nativeCandNext old postE false).alpha = true ∧
       (nativeCandNext old postE false).m = false ∧
       postE.sg = false) := by
  cases hm : old.candidate.m with
  | true =>
      exact Or.inl (matureExitErases old postE false hc hm hl hb)
  | false =>
      cases hs : postE.sg with
      | true =>
          exact Or.inl (returningSignalErases old postE false
            hc ha hl hb hs)
      | false =>
          have hkeep :
              nativeCandNext old postE false = old.candidate := by
            simp [nativeCandNext, nativeCandSelect, nativeCandPrivate,
              hc, ha, hm, hl, hb, hs]
          right
          rw [hkeep]
          exact ⟨hc, ha, hm, rfl⟩

/-- A site after the bullet's outward sweep: absent, or occupied
with first credit, no mature credit and still under zero signal. -/
def ReturnCandSite (x : NativeCand) : Prop :=
  x.candidate = zeroCandidate ∨
    (x.candidate.C = true ∧
     x.candidate.alpha = true ∧
     x.candidate.m = false ∧
     x.native.sg = false)

/-- Under a bullet-free post-E row and without an incoming entry,
the return-site invariant is preserved. The proof does not assume
that the new signal remains zero: when it first becomes one K2
erases the armed record. -/
theorem returnCandLocalNext (old : NativeCand)
    (postE : CertNative)
    (hb : postE.b = (0 : Fin 3))
    (h : ReturnCandSite old) :
    ReturnCandSite
      { native := postE,
        candidate := nativeCandNext old postE false } := by
  change nativeCandNext old postE false = zeroCandidate ∨
    ((nativeCandNext old postE false).C = true ∧
     (nativeCandNext old postE false).alpha = true ∧
     (nativeCandNext old postE false).m = false ∧
     postE.sg = false)
  rcases h with hzero | ⟨hc, ha, _, _⟩
  · exact Or.inl (nativeCandNext_empty old postE false hzero)
  · cases hl : postE.l with
    | true =>
        exact Or.inl (postLeaderErases old postE false hl)
    | false =>
        exact candidateBulletExit old postE hc ha hl hb

/-- Pointwise zero-origin closure is not enough for this lemma.
Instead the nonzero sector may contain an armed but immature
candidate; a return-wave service either retains or erases it. -/
theorem returnCandPair (x y : NativeCand)
    (hx : ReturnCandSite x)
    (hy : ReturnCandSite y)
    (hout : outBullet x.native = 0)
    (hbx : (certLiteralEPair x.native y.native).1.b =
      (0 : Fin 3))
    (hby : (certLiteralEPair x.native y.native).2.b =
      (0 : Fin 3)) :
    ReturnCandSite (birthFreeCandidatePair x y).1 ∧
      ReturnCandSite (birthFreeCandidatePair x y).2 := by
  have henter :
      (!y.native.l && decide (outBullet x.native > 0)) = false := by
    simp [hout]
  constructor
  · change ReturnCandSite
      ({ native := (certLiteralEPair x.native y.native).1,
         candidate := nativeCandNext x
           (certLiteralEPair x.native y.native).1 false } : NativeCand)
    exact returnCandLocalNext x
      (certLiteralEPair x.native y.native).1 hbx hx
  · change ReturnCandSite
      ({ native := (certLiteralEPair x.native y.native).2,
         candidate := nativeCandNext y
           (certLiteralEPair x.native y.native).2
           (!y.native.l && decide (outBullet x.native > 0)) } : NativeCand)
    rw [henter]
    exact returnCandLocalNext y
      (certLiteralEPair x.native y.native).2 hby hy

/-- Purely local lifting of the return-site invariant to a
whole edge; the two post-E bullet-zero hypotheses are passed as
the genuine, computed native projection of this edge. -/
theorem returnCandEdge {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (S : Fin n → NativeCand) (e : Fin n)
    (hS : ∀ i : Fin n, ReturnCandSite (S i))
    (hpost : ∀ i : Fin n,
      (birthFreeCandidateStep ring S e i).native.b = (0 : Fin 3))
    (hout : outBullet (S e).native = 0) :
    ∀ i : Fin n,
      ReturnCandSite (birthFreeCandidateStep ring S e i) := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  have hbx :
      (certLiteralEPair (S e).native
        (S (ring.rightNeighbor e)).native).1.b = (0 : Fin 3) := by
    have hh := hpost e
    simpa [birthFreeCandidateStep, birthFreeCandidatePair] using hh
  have hby :
      (certLiteralEPair (S e).native
        (S (ring.rightNeighbor e)).native).2.b = (0 : Fin 3) := by
    have hh := hpost (ring.rightNeighbor e)
    simpa [birthFreeCandidateStep, birthFreeCandidatePair, hne]
      using hh
  have hp := returnCandPair (S e) (S (ring.rightNeighbor e))
    (hS e) (hS (ring.rightNeighbor e)) hout hbx hby
  intro i
  by_cases he : i = e
  · subst i
    simpa [birthFreeCandidateStep] using hp.1
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      simpa [birthFreeCandidateStep, hne] using hp.2
    · simpa [birthFreeCandidateStep, he, hj] using hS i

/-- Strong return-wave invariant on the same projected history.
ReturnGood is the native suffix invariant; the second
conjunct records the relevant candidate history at each site. -/
def CandidateReturnGood {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → NativeCand) : Prop :=
  ReferencePreparationTrail.ReturnGood ring root (candidateNative S) ∧
    ∀ i : Fin n, ReturnCandSite (S i)

/-- The root is quiet and the native word is bullet-free before
the first ready cut, so there is no incoming entry and every post
bullet remains zero. The candidate erasure rule preserves the
return invariant through arbitrary interleaved selected edges. -/
theorem returnCandQuietStep {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → NativeCand)
    (e : Fin n)
    (hnative : ReferencePreparationTrail.ReturnGood
      ring root (candidateNative S))
    (hz : (candidateNative S root).sg = false)
    (hcand : ∀ i : Fin n, ReturnCandSite (S i)) :
    ∀ i : Fin n, ReturnCandSite
      (birthFreeCandidateStep ring S e i) := by
  have hquiet := ReferencePreparationTrail.beforeReadyStep
    hn ring root (candidateNative S) e hnative.1 hnative.2.1 hz
  have hproj :
      candidateNative (birthFreeCandidateStep ring S e) =
        nativeE ring (candidateNative S) e :=
    birthFreeCandidateStep_native (by omega : 2 ≤ n) ring S e
  have hpost : ∀ i : Fin n,
      (birthFreeCandidateStep ring S e i).native.b = (0 : Fin 3) := by
    intro i
    have hh := hquiet.2.1 i
    rw [← hproj] at hh
    exact hh
  have hout : outBullet (S e).native = 0 := by
    have hb : (S e).native.b = (0 : Fin 3) := hnative.2.1 e
    cases hl : (S e).native.l with
    | false =>
        simp [outBullet, hl, hb]
    | true =>
        cases hs : (S e).native.sg with
        | false =>
            simp [outBullet, hl, hs, hb]
        | true =>
            exact False.elim (hquiet.1 e ⟨hl, hs⟩)
  exact returnCandEdge (by omega : 2 ≤ n) ring
    S e hcand hpost hout

/-- Both native return geometry and candidate retirement stay
synchronized at every quiet step, including the final step which
first makes the root signal one. -/
theorem candidateReturnGoodStep {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → NativeCand)
    (e : Fin n)
    (h : CandidateReturnGood ring root S)
    (hz : (candidateNative S root).sg = false) :
    CandidateReturnGood ring root
      (birthFreeCandidateStep ring S e) := by
  constructor
  · rw [birthFreeCandidateStep_native
      (by omega : 2 ≤ n) ring S e]
    exact ReferencePreparationTrail.returnGoodStep
      hn ring root (candidateNative S) e h.1 hz
  · exact returnCandQuietStep hn ring root S e h.1 hz h.2

/-- At the end of the return wave every native signal is one.
The only possible nonzero candidate under the sweep invariant
would require its own signal to be zero, a contradiction. -/
theorem returnCandAllSignalsEmpty {n : Nat}
    (S : Fin n → NativeCand)
    (h : ∀ i : Fin n, ReturnCandSite (S i))
    (hs : ∀ i : Fin n, (S i).native.sg = true) :
    EmptyCandidates S := by
  intro i
  rcases h i with hz | ⟨_, _, _, hzero⟩
  · exact hz
  · have hone := hs i
    rw [hzero] at hone
    cases hone

/-- At a completed native return, candidate emptiness is a theorem
from the historical candidate invariant, not an extra endpoint
assumption. -/
theorem candidateReturnGoodReady {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → NativeCand)
    (h : CandidateReturnGood ring root S)
    (hp : ReferencePreparationNativePreparedAt root
      (candidateNative S)) :
    EmptyCandidates S := by
  exact returnCandAllSignalsEmpty S h.2
    (fun i => (hp.2.2 i).2)

/-- This target is the intersection of native readiness and the
fully empty candidate factor, at the SAME projected state. -/
def CandidateReturnTarget {n : Nat}
    (root : Fin n) (S : Fin n → NativeCand) : Prop :=
  ReferencePreparationNativePreparedAt root (candidateNative S) ∧
    EmptyCandidates S

/-- Important finite-horizon cost domination: on a GOOD return
history, the first native-prepared hit is automatically a true
candidate-zero hit. It therefore costs no more than the purely
native first hit on the exact same birth-free edge map. -/
theorem candidateReturnCostLeNative {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n) (root : Fin n) :
    ∀ T (S : Fin n → NativeCand),
      CandidateReturnGood ring root S →
      costNumerator (birthFreeCandidateStep ring)
        (CandidateReturnTarget root) S T ≤
      costNumerator (nativeE ring)
        (ReferencePreparationNativePreparedAt root)
        (candidateNative S) T := by
  classical
  intro T
  induction T with
  | zero =>
      intro S _
      simp only [costNumerator_zero]
      exact Nat.le_refl 0
  | succ T ih =>
      intro S h
      by_cases hp : ReferencePreparationNativePreparedAt
          root (candidateNative S)
      · have hc : CandidateReturnTarget root S :=
          ⟨hp, candidateReturnGoodReady ring root S h hp⟩
        rw [costNumerator_terminal (birthFreeCandidateStep ring)
          (CandidateReturnTarget root) S hc (T + 1)]
        exact Nat.zero_le _
      · have hnot : ¬ CandidateReturnTarget root S := by
          intro hc
          exact hp hc.1
        have hz : (candidateNative S root).sg = false := by
          cases hs : (candidateNative S root).sg with
          | false =>
              rfl
          | true =>
              exact False.elim (hp
                (ReferencePreparationTrail.returnPreparedIfReady
                  ring root (candidateNative S) h.1 hs))
        rw [costNumerator_succ (birthFreeCandidateStep ring)
          (CandidateReturnTarget root) S hnot T,
          costNumerator_succ (nativeE ring)
            (ReferencePreparationNativePreparedAt root)
            (candidateNative S) hp T]
        exact Nat.add_le_add_left
          (ofFn_sum_le
            (fun e : Fin n =>
              costNumerator (birthFreeCandidateStep ring)
                (CandidateReturnTarget root)
                (birthFreeCandidateStep ring S e) T)
            (fun e : Fin n =>
              costNumerator (nativeE ring)
                (ReferencePreparationNativePreparedAt root)
                (nativeE ring (candidateNative S) e) T)
            (fun e => by
              have hchild := ih (birthFreeCandidateStep ring S e)
                (candidateReturnGoodStep hn ring root S e h hz)
              rw [birthFreeCandidateStep_native
                (by omega : 2 ≤ n) ring S e] at hchild
              exact hchild)) _

/-- Post-absorption return: a proved n^2 bound once the forward
sweep invariant has actually been established. This bound is on
the exact projected birth-free map, not an invented full-state
protocol or an unguarded physical run. -/
theorem candidateAbsorbedReturnCost {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → NativeCand)
    (hnative : ReferencePreparationTrail.AbsorbedCut
      ring root (candidateNative S))
    (hcand : ∀ i : Fin n, ReturnCandSite (S i))
    (T : Nat) :
    costNumerator (birthFreeCandidateStep ring)
      (CandidateReturnTarget root) S T ≤ n ^ T * n ^ 2 := by
  have hgood := ReferencePreparationTrail.absorbedReturnGood
    hn ring root (candidateNative S) hnative
  exact Nat.le_trans
    (candidateReturnCostLeNative hn ring root T S
      ⟨hgood, hcand⟩)
    (ReferencePreparationTrail.absorptionReturnCost hn
      ring root (candidateNative S) hnative T)

/-- The exact same conditional n^2 return bound in doubled
integer form, with no rounding of partial expected values. -/
theorem candidateAbsorbedReturnDoubledCost {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → NativeCand)
    (hnative : ReferencePreparationTrail.AbsorbedCut
      ring root (candidateNative S))
    (hcand : ∀ i : Fin n, ReturnCandSite (S i))
    (T : Nat) :
    2 * costNumerator (birthFreeCandidateStep ring)
      (CandidateReturnTarget root) S T ≤
      n ^ T * (2 * n ^ 2) := by
  have hc := candidateAbsorbedReturnCost
    hn ring root S hnative hcand T
  calc
    2 * costNumerator (birthFreeCandidateStep ring)
        (CandidateReturnTarget root) S T ≤
      2 * (n ^ T * n ^ 2) := Nat.mul_le_mul_left 2 hc
    _ = n ^ T * (2 * n ^ 2) := by ac_rfl

/-- A native-prepared singleton is a real ReadyCut; unlike
the first-hit stopping theorem, this fact makes the next
incident firing available to the fresh-circulation clock. -/
theorem nativePreparedReady {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (N : TripleNativeState n)
    (hp : ReferencePreparationNativePreparedAt root N)
    (hprotected : Protected ring N) :
    ReferencePreparationTrail.ReadyCut ring root N := by
  exact ⟨⟨hp.1, hp.2.1, hprotected⟩,
    (fun i => (hp.2.2 i).1), (hp.2.2 root).2⟩

/-- OUTGOING incident service: the distinguished live bullet
starts at offset one, under the native row theorem. -/
theorem nativePreparedOutgoingFires {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n)
    (hp : ReferencePreparationNativePreparedAt root N)
    (hprotected : Protected ring N) :
    ReferencePreparationTrail.FiredCut
      ring root (nativeE ring N root) := by
  have hr := nativePreparedReady ring root N hp hprotected
  exact ⟨ReferencePreparationTrail.rootedStep
    hn ring root N root hr.1, 1,
    (ReferencePreparationTrail.freshOutgoing hn
      ring root N hr).1⟩

/-- INCOMING incident service: the distinguished dummy bullet
starts at offset zero, not at the previous follower. -/
theorem nativePreparedIncomingFires {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root e : Fin n) (N : TripleNativeState n)
    (hp : ReferencePreparationNativePreparedAt root N)
    (hprotected : Protected ring N)
    (hj : ring.rightNeighbor e = root) :
    ReferencePreparationTrail.FiredCut
      ring root (nativeE ring N e) := by
  have hr := nativePreparedReady ring root N hp hprotected
  exact ⟨ReferencePreparationTrail.rootedStep
    hn ring root N e hr.1, 0,
    (ReferencePreparationTrail.freshIncoming hn
      ring root e N hr hj).1⟩

/-- A fresh incident edge really fires on a physical headline
configuration when the exact OLD FIRE test is none. We rewrite
the native equality as a hypothesis, not the abstract
HeadlineConfiguration protocol-step expression. -/
theorem physicalPreparedOutgoingFires {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (C : HeadlineConfiguration n)
    (hp : ReferencePreparationNativePreparedAt root
      (nativeProjection C))
    (hprotected : Protected ring (nativeProjection C))
    (hfire : NativeLiftNoFireOn ring C root) :
    ReferencePreparationTrail.FiredCut ring root
      (nativeProjection (headlinePhysicalNext ring C root)) := by
  have hnative := nativePreparedOutgoingFires hn
    ring root (nativeProjection C) hp hprotected
  have hstep := native_lift_no_fire_step
    (by omega : 3 ≤ n) ring C root hfire
  rw [← hstep] at hnative
  exact hnative

/-- Ready -> first distinguished absorption: the real n/2
incident clock plus the n^2 bullet traversal, in doubled form.
This is a native estimate; the forward candidate sweep invariant
has NOT yet been proved from arbitrary candidate records. -/
theorem readyToAbsorptionDoubledCost {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n)
    (hready : ReferencePreparationTrail.ReadyCut ring root N)
    (T : Nat) :
    2 * costNumerator (nativeE ring)
      (ReferencePreparationTrail.AbsorbedCut ring root) N T ≤
      n ^ T * (2 * n ^ 2 + n) := by
  have hfirst : ∀ U,
      2 * costNumerator (nativeE ring)
        (fun x => ReferencePreparationTrail.FiredCut ring root x ∨
          ReferencePreparationTrail.AbsorbedCut ring root x)
        N U ≤ n ^ U * n := by
    intro U
    exact Nat.le_trans
      (Nat.mul_le_mul_left 2
        (Prob.costNumerator_target_mono (nativeE ring)
          (ReferencePreparationTrail.FiredCut ring root)
          (fun x => ReferencePreparationTrail.FiredCut ring root x ∨
            ReferencePreparationTrail.AbsorbedCut ring root x)
          (by intro x hx; exact Or.inl hx) N U))
      (ReferencePreparationTrail.freshHalfCost
        hn ring root N hready U)
  have hsecond : ∀ z,
      ReferencePreparationTrail.FiredCut ring root z →
      ∀ U, 2 * costNumerator (nativeE ring)
        (ReferencePreparationTrail.AbsorbedCut ring root) z U ≤
        n ^ U * (2 * n ^ 2) := by
    intro z hz U
    have hc := ReferencePreparationTrail.circulationCost
      hn ring root z hz U
    calc
      2 * costNumerator (nativeE ring)
          (ReferencePreparationTrail.AbsorbedCut ring root) z U ≤
        2 * (n ^ U * n ^ 2) := Nat.mul_le_mul_left 2 hc
      _ = n ^ U * (2 * n ^ 2) := by ac_rfl
  have hc := ReferencePreparationTrail.doubledStageCost
    (nativeE ring) N
    (ReferencePreparationTrail.FiredCut ring root)
    (ReferencePreparationTrail.AbsorbedCut ring root)
    n (2 * n ^ 2) hfirst hsecond T
  exact Nat.le_trans hc
    (Nat.mul_le_mul_left (n ^ T)
      (by omega : n + 2 * n ^ 2 ≤ 2 * n ^ 2 + n))

/-- This is a *logical accounting identity*, not an unconditional
physical preparation certificate. The three fresh stages together
have doubled reserve 4n^2+n, hence re-running them after the old
first-native-prepared hit raises the ledger to 14n^2+2n. -/
theorem postNativePreparedBudget (n : Nat) :
    (2 * n ^ 2 + n) + 2 * n ^ 2 =
      4 * n ^ 2 + n := by
  omega

theorem postNativePreparedTotalBudget (n : Nat) :
    (10 * n ^ 2 + n) + (4 * n ^ 2 + n) =
      14 * n ^ 2 + 2 * n := by
  omega

theorem postNativePreparedExceedsHeadline (n : Nat)
    (hn : 5 ≤ n) :
    10 * n ^ 2 + n < 14 * n ^ 2 + 2 * n := by
  omega

/-- Proof-only prefix guard: every edge of the return interval
is taken while the root's OLD signal is still zero. The last edge
may be precisely the first one that makes the root ready. -/
def CandidateReturnQuietWord {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    (Fin n → NativeCand) → List (Fin n) → Prop
  | _, [] => True
  | S, e :: es =>
      (candidateNative S root).sg = false ∧
        CandidateReturnQuietWord ring root
          (birthFreeCandidateStep ring S e) es

/-- The historical candidate-return invariant survives every
nonterminal-prefix edge, with no assumption of consecutive
scheduler services. -/
theorem candidateReturnGoodWord {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) :
    ∀ (edges : List (Fin n)) (S : Fin n → NativeCand),
      CandidateReturnGood ring root S →
      CandidateReturnQuietWord ring root S edges →
      CandidateReturnGood ring root (candidateWord ring S edges) := by
  intro edges
  induction edges with
  | nil =>
      intro S h _
      exact h
  | cons e es ih =>
      intro S h hquiet
      change CandidateReturnGood ring root
        (candidateWord ring (birthFreeCandidateStep ring S e) es)
      exact ih (birthFreeCandidateStep ring S e)
        (candidateReturnGoodStep hn ring root S e h hquiet.1)
        hquiet.2

/-- From the genuine return-wave history, the later physical
native-prepared cut has zero candidates. The old handoff theorem
is reused; no EmptyCandidates premise appears in this statement. -/
theorem handoffFromReturnSweep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : HeadlineConfiguration n)
    (hnative : ReferencePreparationNativePreparedAt
      root (nativeProjection C))
    (hprotected : Protected ring (nativeProjection C))
    (hgrant : NativeLiftGrantFree C)
    (hclean : C_native ring (nativeProjection C))
    (hcand : ∀ i : Fin n,
      ReturnCandSite (physicalCandidates C i)) :
    ReferencePreparationPreparedCore ring C := by
  have hzero : EmptyCandidates (physicalCandidates C) :=
    returnCandAllSignalsEmpty (physicalCandidates C) hcand
      (fun i => (hnative.2.2 i).2)
  exact ReferencePreparationTrail.nativePreparedPhysicalCandidateHandoff
    ring root C hnative hprotected hgrant hclean hzero

/-- A pathwise physical handoff: the return-wave invariant at the
actual post-absorption origin and the actual no-FIRE word certify
the candidate-zero target at the first native-ready endpoint.
The required return history is exposed rather than fabricated. -/
theorem handoffFromPhysicalReturnWord {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n) (root : Fin n)
    (C : HeadlineConfiguration n) (edges : List (Fin n))
    (hstart : CandidateReturnGood ring root
      (physicalCandidates C))
    (hquiet : CandidateReturnQuietWord ring root
      (physicalCandidates C) edges)
    (hword : NativeLiftNoFireWord ring C edges)
    (hnative : ReferencePreparationNativePreparedAt root
      (nativeProjection (nativeLiftRealRun ring C edges)))
    (hprotected : Protected ring
      (nativeProjection (nativeLiftRealRun ring C edges)))
    (hgrant : NativeLiftGrantFree
      (nativeLiftRealRun ring C edges))
    (hclean : C_native ring
      (nativeProjection (nativeLiftRealRun ring C edges))) :
    ReferencePreparationPreparedCore ring
      (nativeLiftRealRun ring C edges) := by
  have hgood := candidateReturnGoodWord hn ring root edges
    (physicalCandidates C) hstart hquiet
  have hprojection := noFirePhysicalWord hn ring C edges hword
  rw [← hprojection] at hgood
  exact handoffFromReturnSweep ring root
    (nativeLiftRealRun ring C edges)
    hnative hprotected hgrant hclean hgood.2

end ReferencePreparationCandidate
end L3


/-!
Forward-sweep candidate invariants.

The prefix invariant is deliberately
indexed by the actual distinguished native bullet (SingleAt), and
all services below are the existing birthFreeCandidateStep = Phi_e.
The full nominated-edge and physical cost bridge are not asserted
without their missing global proof.
-/

namespace L3
namespace ReferencePreparationTrail

open ReferencePreparationCandidate
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- At the bullet host, an occupied record is first-armed but may
still have mature credit. Exactly the right intermediate condition:
mature records are deleted when the bullet leaves. -/
def CandidateSweepHost (x : NativeCand) : Prop :=
  x.candidate = zeroCandidate ∨
    (x.candidate.C = true ∧ x.candidate.alpha = true)

/-- The real swept prefix: sites strictly before the bullet have
completed its outgoing service; the host has received the bullet.
The native zero trail is supplied separately by SingleAt. -/
def CandidateSweptPrefix {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → NativeCand) (p : Nat) : Prop :=
  (∀ k : Nat, k < p →
    ReturnCandSite (S (PPL.shiftRight ring root k))) ∧
  CandidateSweepHost (S (PPL.shiftRight ring root p))

/-- No claim about unswept candidates: they may have arbitrary
occupancy, first-credit and mature-credit values. -/
def CandidateSweepState {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → NativeCand) (p : Nat) : Prop :=
  Rooted ring root (candidateNative S) ∧
  SingleAt ring root (candidateNative S) p ∧
  CandidateSweptPrefix ring root S p

/-- At the full physical absorption service, all sites must have
become return-wave compatible. This target is stronger than the
native AbsorbedCut, and is a state-only consequence of a genuinely
completed annotated sweep, not an arbitrary native entrance. -/
def CandidateSweepAbsorbed {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → NativeCand) : Prop :=
  AbsorbedCut ring root (candidateNative S) ∧
    ∀ i : Fin n, ReturnCandSite (S i)

/-- Any serviced already-armed host remains armed or is completely
erased, irrespective of its old mature bit or incoming entry flag.
An empty host cannot acquire occupancy. -/
theorem candidateSweepHostNext (old : NativeCand)
    (postE : CertNative) (enter : Bool)
    (h : CandidateSweepHost old) :
    CandidateSweepHost
      { native := postE,
        candidate := nativeCandNext old postE enter } := by
  change nativeCandNext old postE enter = zeroCandidate ∨
    ((nativeCandNext old postE enter).C = true ∧
     (nativeCandNext old postE enter).alpha = true)
  rcases h with hz | ⟨hc, ha⟩
  · exact Or.inl (nativeCandNext_empty old postE enter hz)
  · cases hs : nativeCandSelect old postE enter <;>
      simp [nativeCandNext, nativeCandPrivate, hs,
        zeroCandidate, hc, ha]

/-- Any actual birth-free service preserves the armed-or-absent
property at a specified physical site, including if it is source,
responder, or untouched. -/
theorem candidateSweepHostStep {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (S : Fin n → NativeCand) (e i : Fin n)
    (h : CandidateSweepHost (S i)) :
    CandidateSweepHost (birthFreeCandidateStep ring S e i) := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  by_cases he : i = e
  · subst i
    have hs := candidateSweepHostNext (S e)
      (certLiteralEPair (S e).native
        (S (ring.rightNeighbor e)).native).1 false h
    simpa [birthFreeCandidateStep, birthFreeCandidatePair] using hs
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      have hs := candidateSweepHostNext (S (ring.rightNeighbor e))
        (certLiteralEPair (S e).native
          (S (ring.rightNeighbor e)).native).2
        (! (S (ring.rightNeighbor e)).native.l &&
          decide (outBullet (S e).native > 0)) h
      simpa [birthFreeCandidateStep, birthFreeCandidatePair, hne]
        using hs
    · simpa [birthFreeCandidateStep, he, hj] using h

/-- The outgoing source always has post-E bullet zero. If it was
empty, it remains empty; if armed, SAN/K2/PROM either erase it,
or the survivor is first-armed, immature, and signal-zero. -/
theorem candidateSweepExit (old : NativeCand)
    (postE : CertNative)
    (h : CandidateSweepHost old)
    (hb : postE.b = (0 : Fin 3)) :
    ReturnCandSite
      { native := postE,
        candidate := nativeCandNext old postE false } := by
  change nativeCandNext old postE false = zeroCandidate ∨
    ((nativeCandNext old postE false).C = true ∧
     (nativeCandNext old postE false).alpha = true ∧
     (nativeCandNext old postE false).m = false ∧
     postE.sg = false)
  rcases h with hz | ⟨hc, ha⟩
  · exact Or.inl (nativeCandNext_empty old postE false hz)
  · cases hl : postE.l with
    | true =>
        exact Or.inl (postLeaderErases old postE false hl)
    | false =>
        exact candidateBulletExit old postE hc ha hl hb

/-- A nonempty new bullet at a follower with an actual old
incoming entry leaves the candidate either wholly empty or
first-armed. No assumption on inherited old alpha/m is required. -/
theorem candidateSweepEntry (x y : NativeCand)
    (hy : y.native.l = false)
    (hout : 0 < outBullet x.native)
    (hl : (certLiteralEPair x.native y.native).2.l = false)
    (hb : (certLiteralEPair x.native y.native).2.b ≠
      (0 : Fin 3))
    (hs : (certLiteralEPair x.native y.native).2.sg = false) :
    CandidateSweepHost (birthFreeCandidatePair x y).2 := by
  have hkind :
      (certLiteralEPair x.native y.native).2.b =
        (1 : Fin 3) ∨
      (certLiteralEPair x.native y.native).2.b =
        (2 : Fin 3) := by
    generalize (certLiteralEPair x.native y.native).2.b = B at hb ⊢
    rcases B with ⟨v, hv⟩
    rcases v with _ | _ | _ | v
    · exact False.elim (hb rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · omega
  have hentry :
      (!y.native.l && decide (outBullet x.native > 0)) = true := by
    simp [hy, hout]
  change nativeCandNext y
      (certLiteralEPair x.native y.native).2
      (!y.native.l && decide (outBullet x.native > 0)) =
        zeroCandidate ∨
    ((nativeCandNext y (certLiteralEPair x.native y.native).2
        (!y.native.l && decide (outBullet x.native > 0))).C = true ∧
     (nativeCandNext y (certLiteralEPair x.native y.native).2
        (!y.native.l && decide (outBullet x.native > 0))).alpha = true)
  rw [hentry]
  cases hc : y.candidate.C with
  | false =>
      exact Or.inl (candidateNoResurrection y
        (certLiteralEPair x.native y.native).2 true hc)
  | true =>
      exact Or.inr (candidateArrivalArms y
        (certLiteralEPair x.native y.native).2
        hc hl hs hkind)

/-- A fixed site already in the swept prefix remains
return-compatible on a service whose source has no outgoing
bullet/ready firing and whose new local bullet is zero. -/
theorem candidateSweepReturnNoEntry {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (S : Fin n → NativeCand) (e i : Fin n)
    (hout : outBullet (S e).native = 0)
    (hold : ReturnCandSite (S i))
    (hb : (birthFreeCandidateStep ring S e i).native.b =
      (0 : Fin 3)) :
    ReturnCandSite (birthFreeCandidateStep ring S e i) := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  by_cases he : i = e
  · subst i
    have hpost :
        (certLiteralEPair (S e).native
          (S (ring.rightNeighbor e)).native).1.b = (0 : Fin 3) := by
      simpa [birthFreeCandidateStep,
        birthFreeCandidatePair] using hb
    have hloc := returnCandLocalNext (S e)
      (certLiteralEPair (S e).native
        (S (ring.rightNeighbor e)).native).1 hpost hold
    simpa [birthFreeCandidateStep, birthFreeCandidatePair]
      using hloc
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      have hpost :
          (certLiteralEPair (S e).native
            (S (ring.rightNeighbor e)).native).2.b =
              (0 : Fin 3) := by
        simpa [birthFreeCandidateStep,
          birthFreeCandidatePair, hne] using hb
      have hloc := returnCandLocalNext
        (S (ring.rightNeighbor e))
        (certLiteralEPair (S e).native
          (S (ring.rightNeighbor e)).native).2
        hpost hold
      have hentry :
          (! (S (ring.rightNeighbor e)).native.l &&
            decide (outBullet (S e).native > 0)) = false := by
        simp [hout]
      simpa [birthFreeCandidateStep, birthFreeCandidatePair,
        hne, hentry] using hloc
    · simpa [birthFreeCandidateStep, he, hj] using hold

/-- Away from the distinguished bullet host, no old bullet leaves
the initiator and no leader can newly fire: the actual SingleAt
zero trail keeps the unique leader's signal zero. -/
theorem candidateSweepOtherSourceQuiet {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → NativeCand)
    (p : Nat) (e : Fin n)
    (hu : ∀ i : Fin n, (candidateNative S i).l = true →
      i = root)
    (hsingle : SingleAt ring root (candidateNative S) p)
    (he : e ≠ PPL.shiftRight ring root p) :
    outBullet (S e).native = 0 := by
  have hb : (S e).native.b = (0 : Fin 3) :=
    hsingle.2.2.1 e he
  have hz := trailRootZero ring root (candidateNative S) p
    hsingle.2.2.2
  have hq := noFire (candidateNative S) root hu hz e
  cases hl : (S e).native.l with
  | false =>
      simp [outBullet, hl, hb]
  | true =>
      cases hsig : (S e).native.sg with
      | false =>
          simp [outBullet, hl, hsig, hb]
      | true =>
          exact False.elim (hq ⟨hl, hsig⟩)

/-- The candidate sweep is preserved by EVERY non-nominated
birth-free service, including an edge immediately before the
bullet host. All native signal and bullet obligations are obtained
from the existing SingleAt.singleStay, not guessed from
the informal paper picture. -/
theorem candidateSweepNonHostStep {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → NativeCand)
    (p : Nat) (e : Fin n)
    (h : CandidateSweepState ring root S p)
    (he : e ≠ PPL.shiftRight ring root p) :
    CandidateSweepState ring root
      (birthFreeCandidateStep ring S e) p := by
  have hnproj : candidateNative
      (birthFreeCandidateStep ring S e) =
      nativeE ring (candidateNative S) e :=
    birthFreeCandidateStep_native (by omega : 2 ≤ n) ring S e
  have hroot := rootedStep hn ring root
    (candidateNative S) e h.1
  have hsingle := singleStay hn ring root
    (candidateNative S) p e h.1.2.1 h.2.1 he
  have hout := candidateSweepOtherSourceQuiet ring root S p
    e h.1.2.1 h.2.1 he
  refine ⟨?_, ?_, ?_⟩
  · rw [hnproj]
    exact hroot
  · rw [hnproj]
    exact hsingle
  · constructor
    · intro k hk
      have hsite :
          PPL.shiftRight ring root k ≠
            PPL.shiftRight ring root p := by
        intro heq
        have hv := shiftInjective ring root k p
          (by have hp' := h.2.1.1; omega) h.2.1.1 heq
        omega
      have hb :
          (birthFreeCandidateStep ring S e
            (PPL.shiftRight ring root k)).native.b =
              (0 : Fin 3) := by
        have hv := hsingle.2.2.1
          (PPL.shiftRight ring root k) hsite
        rw [← hnproj] at hv
        exact hv
      exact candidateSweepReturnNoEntry
        (by omega : 2 ≤ n) ring S e
        (PPL.shiftRight ring root k)
        hout (h.2.2.1 k hk) hb
    · exact candidateSweepHostStep
        (by omega : 2 ≤ n) ring S e
        (PPL.shiftRight ring root p) h.2.2.2

/-- A bullet at the current host supplies a positive old
outgoing entry test even when its native kind is dummy. The
zero-trail condition precludes the ready-leader alternative. -/
theorem candidateSweepHostOutgoing {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → NativeCand) (p : Nat)
    (hsingle : SingleAt ring root (candidateNative S) p) :
    0 < outBullet (S (PPL.shiftRight ring root p)).native := by
  have hsig := hsingle.2.2.2 p (Nat.le_refl p)
  have hb := hsingle.2.1
  have hv :
      0 < (S (PPL.shiftRight ring root p)).native.b.val := by
    by_cases hzero :
        (S (PPL.shiftRight ring root p)).native.b.val = 0
    · have heq :
          (S (PPL.shiftRight ring root p)).native.b =
            (0 : Fin 3) := Fin.ext hzero
      exact False.elim (hb heq)
    · omega
  cases hl : (S (PPL.shiftRight ring root p)).native.l with
  | false =>
      simpa [outBullet, hl] using hv
  | true =>
      simp only [outBullet, hl]
      split <;> omega

/-- The exact arithmetic of the ORIGINAL H.1 six-stage
history: first readiness must not be paid twice. This lemma
is a budget identity only and does not silently establish a
full physical expected-hitting-time theorem. -/
theorem candidateSweepOriginalBudget (n : Nat) :
    6 * n ^ 2 + n + 2 * n ^ 2 + 2 * n ^ 2 =
      10 * n ^ 2 + n := by
  omega

/-- Re-running a complete fresh circulation AFTER a first
native-only prepared cut gives the larger ledger of the earlier construction.
This is not the sharp phase-aligned construction. -/
theorem candidateSweepRestartBudget (n : Nat) :
    (10 * n ^ 2 + n) + (4 * n ^ 2 + n) =
      14 * n ^ 2 + 2 * n := by
  omega

end ReferencePreparationTrail
end L3


/-!
Nominated forward sweep and the phase-aware absorption clock.

No import, alteration to the existing
file, new axiom, or replacement protocol transition is introduced.
-/

namespace L3
namespace ReferencePreparationTrail

open ReferencePreparationCandidate
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- A frame equation for the actual birth-disabled candidate map. -/
theorem candidateSweepFrame {n : Nat}
    (ring : DirectedRing n) (S : Fin n → NativeCand)
    (e i : Fin n) (he : i ≠ e)
    (hj : i ≠ ring.rightNeighbor e) :
    birthFreeCandidateStep ring S e i = S i := by
  simp [birthFreeCandidateStep, he, hj]

/-- Any selected service touching the unique post-update leader
erases its candidate by SAN. The two branches cover outgoing
and incoming incident edges, including the dummy firing. -/
theorem candidateSweepRootSan {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → NativeCand)
    (e : Fin n)
    (hroot : (nativeE ring (candidateNative S) e root).l = true)
    (hincident : e = root ∨ ring.rightNeighbor e = root) :
    ReturnCandSite (birthFreeCandidateStep ring S e root) := by
  rcases hincident with he | hj
  · subst e
    have hpair := sealed_prep_actual_old_pair ring
      (candidateNative S) root (rightNe hn ring root)
    have hl :
        (certLiteralEPair (S root).native
          (S (ring.rightNeighbor root)).native).1.l = true := by
      rw [hpair.1] at hroot
      exact hroot
    have hzero :
        (birthFreeCandidatePair
          (S root) (S (ring.rightNeighbor root))).1.candidate =
            zeroCandidate := by
      change nativeCandNext (S root)
        (certLiteralEPair (S root).native
          (S (ring.rightNeighbor root)).native).1 false =
            zeroCandidate
      exact postLeaderErases (S root)
        (certLiteralEPair (S root).native
          (S (ring.rightNeighbor root)).native).1 false hl
    have hs : ReturnCandSite
        (birthFreeCandidatePair
          (S root) (S (ring.rightNeighbor root))).1 :=
      Or.inl hzero
    simpa [birthFreeCandidateStep] using hs
  · have hne := rightNe hn ring e
    have hpair := sealed_prep_actual_old_pair ring
      (candidateNative S) e hne
    have hl :
        (certLiteralEPair (S e).native
          (S (ring.rightNeighbor e)).native).2.l = true := by
      rw [← hj, hpair.2] at hroot
      exact hroot
    have hzero :
        (birthFreeCandidatePair
          (S e) (S (ring.rightNeighbor e))).2.candidate =
            zeroCandidate := by
      change nativeCandNext (S (ring.rightNeighbor e))
        (certLiteralEPair (S e).native
          (S (ring.rightNeighbor e)).native).2
        (! (S (ring.rightNeighbor e)).native.l &&
          decide (outBullet (S e).native > 0)) = zeroCandidate
      exact postLeaderErases (S (ring.rightNeighbor e))
        (certLiteralEPair (S e).native
          (S (ring.rightNeighbor e)).native).2
        (! (S (ring.rightNeighbor e)).native.l &&
          decide (outBullet (S e).native > 0)) hl
    have hs : ReturnCandSite
        (birthFreeCandidatePair
          (S e) (S (ring.rightNeighbor e))).2 :=
      Or.inl hzero
    rw [← hj]
    simpa [birthFreeCandidateStep, hne] using hs

/-- A nonempty or already-armed return record is also a valid
sweep host; the host invariant intentionally does not test mature
credit or the local signal. -/
theorem candidateReturnHost (x : NativeCand)
    (h : ReturnCandSite x) : CandidateSweepHost x := by
  rcases h with hz | ⟨hc, ha, _, _⟩
  · exact Or.inl hz
  · exact Or.inr ⟨hc, ha⟩

/-- Interior nominated service. The current distinguished bullet
exits offset p and enters offset p+1. All earlier sites frame,
except for p which is retired by the *same* source service. -/
theorem candidateSweepInteriorStep {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → NativeCand)
    (p : Nat)
    (h : CandidateSweepState ring root S p)
    (hnext : p + 1 < n) :
    CandidateSweepState ring root
      (birthFreeCandidateStep ring S
        (PPL.shiftRight ring root p)) (p + 1) := by
  have hj :
      ring.rightNeighbor (PPL.shiftRight ring root p) =
        PPL.shiftRight ring root (p + 1) :=
    (referencePreparationShiftSucc ring root p).symm
  have hne := rightNe hn ring (PPL.shiftRight ring root p)
  have hpair := sealed_prep_actual_old_pair ring
    (candidateNative S) (PPL.shiftRight ring root p) hne
  have hproj :
      candidateNative
        (birthFreeCandidateStep ring S
          (PPL.shiftRight ring root p)) =
        nativeE ring (candidateNative S)
          (PPL.shiftRight ring root p) :=
    birthFreeCandidateStep_native (by omega : 2 ≤ n)
      ring S (PPL.shiftRight ring root p)
  have hroot := rootedStep hn ring root (candidateNative S)
    (PPL.shiftRight ring root p) h.1
  have hsingle := singleForward hn ring root
    (candidateNative S) p h.1 h.2.1 hnext
  have hnotRoot :
      ring.rightNeighbor (PPL.shiftRight ring root p) ≠ root := by
    rw [hj]
    exact referencePreparation_sealed_site_ne
      ring root (p + 1) (by omega) hnext
  have hy :
      (S (ring.rightNeighbor
        (PPL.shiftRight ring root p))).native.l = false :=
    follower (candidateNative S) root _ h.1.2.1 hnotRoot
  have hout := candidateSweepHostOutgoing ring root S p h.2.1
  have hl :
      (certLiteralEPair
        (S (PPL.shiftRight ring root p)).native
        (S (ring.rightNeighbor
          (PPL.shiftRight ring root p))).native).2.l = false := by
    have hh := follower
      (nativeE ring (candidateNative S)
        (PPL.shiftRight ring root p))
      root (ring.rightNeighbor (PPL.shiftRight ring root p))
      hroot.2.1 hnotRoot
    rw [hpair.2] at hh
    exact hh
  have hb :
      (certLiteralEPair
        (S (PPL.shiftRight ring root p)).native
        (S (ring.rightNeighbor
          (PPL.shiftRight ring root p))).native).2.b ≠
          (0 : Fin 3) := by
    have hh := hsingle.2.1
    rw [← hj, hpair.2] at hh
    exact hh
  have hz :
      (certLiteralEPair
        (S (PPL.shiftRight ring root p)).native
        (S (ring.rightNeighbor
          (PPL.shiftRight ring root p))).native).2.sg = false := by
    have hh := hsingle.2.2.2 (p + 1) (Nat.le_refl (p + 1))
    rw [← hj, hpair.2] at hh
    exact hh
  have hnewHost : CandidateSweepHost
      (birthFreeCandidateStep ring S
        (PPL.shiftRight ring root p)
        (PPL.shiftRight ring root (p + 1))) := by
    have hh := candidateSweepEntry
      (S (PPL.shiftRight ring root p))
      (S (ring.rightNeighbor (PPL.shiftRight ring root p)))
      hy hout hl hb hz
    rw [← hj]
    simpa [birthFreeCandidateStep, hne] using hh
  have hnewSource : ReturnCandSite
      (birthFreeCandidateStep ring S
        (PPL.shiftRight ring root p)
        (PPL.shiftRight ring root p)) := by
    have hh := candidateSweepExit
      (S (PPL.shiftRight ring root p))
      (certLiteralEPair
        (S (PPL.shiftRight ring root p)).native
        (S (ring.rightNeighbor
          (PPL.shiftRight ring root p))).native).1
      h.2.2.2
      ((literalFacts _ _).source_empty)
    simpa [birthFreeCandidateStep, birthFreeCandidatePair] using hh
  refine ⟨?_, ?_, ?_⟩
  · rw [hproj]
    exact hroot
  · rw [hproj]
    exact hsingle
  · refine ⟨?_, hnewHost⟩
    intro k hk
    by_cases hkp : k < p
    · have hsrc :
          PPL.shiftRight ring root k ≠
            PPL.shiftRight ring root p := by
        intro he
        have hv := shiftInjective ring root k p
          (by have hbound := h.2.1.1; omega)
          h.2.1.1 he
        omega
      have hdst :
          PPL.shiftRight ring root k ≠
            ring.rightNeighbor (PPL.shiftRight ring root p) := by
        rw [hj]
        intro he
        have hv := shiftInjective ring root k (p + 1)
          (by omega) hnext he
        omega
      rw [candidateSweepFrame ring S
        (PPL.shiftRight ring root p)
        (PPL.shiftRight ring root k) hsrc hdst]
      exact h.2.2.1 k hkp
    · have hkeq : k = p := by omega
      rw [hkeq]
      exact hnewSource

/-- Final nominated service at offset n-1. The current host
retires on its source update, the root is SAN-erased as responder,
and every other swept site is framed. This is *the* actual
distinguished-bullet absorption, not a native lookalike cut. -/
theorem candidateSweepFinalStep {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → NativeCand)
    (p : Nat)
    (h : CandidateSweepState ring root S p)
    (hlast : p + 1 = n) :
    CandidateSweepAbsorbed ring root
      (birthFreeCandidateStep ring S
        (PPL.shiftRight ring root p)) := by
  have hj :
      ring.rightNeighbor (PPL.shiftRight ring root p) = root := by
    rw [← referencePreparationShiftSucc, hlast, shiftFull]
  have hne := rightNe hn ring (PPL.shiftRight ring root p)
  have hpair := sealed_prep_actual_old_pair ring
    (candidateNative S) (PPL.shiftRight ring root p) hne
  have hproj :
      candidateNative
        (birthFreeCandidateStep ring S
          (PPL.shiftRight ring root p)) =
        nativeE ring (candidateNative S)
          (PPL.shiftRight ring root p) :=
    birthFreeCandidateStep_native (by omega : 2 ≤ n)
      ring S (PPL.shiftRight ring root p)
  have habs := lastAbsorption hn ring root
    (candidateNative S) p h.1 h.2.1 hlast
  have hrootCandidate : ReturnCandSite
      (birthFreeCandidateStep ring S
        (PPL.shiftRight ring root p) root) :=
    candidateSweepRootSan hn ring root S
      (PPL.shiftRight ring root p) habs.1.1 (Or.inr hj)
  have hsource : ReturnCandSite
      (birthFreeCandidateStep ring S
        (PPL.shiftRight ring root p)
        (PPL.shiftRight ring root p)) := by
    have hh := candidateSweepExit
      (S (PPL.shiftRight ring root p))
      (certLiteralEPair
        (S (PPL.shiftRight ring root p)).native
        (S (ring.rightNeighbor
          (PPL.shiftRight ring root p))).native).1
      h.2.2.2
      ((literalFacts _ _).source_empty)
    simpa [birthFreeCandidateStep, birthFreeCandidatePair] using hh
  constructor
  · rw [hproj]
    exact habs
  · intro i
    by_cases he : i = PPL.shiftRight ring root p
    · rw [he]
      exact hsource
    · by_cases hd :
          i = ring.rightNeighbor (PPL.shiftRight ring root p)
      · rw [hd, hj]
        exact hrootCandidate
      · obtain ⟨k, hk, hsite⟩ :=
          referencePreparationShiftSurj ring root i
        have hkne : k ≠ p := by
          intro heq
          rw [heq] at hsite
          exact he hsite.symm
        have hkp : k < p := by omega
        have hbefore : ReturnCandSite (S i) := by
          rw [← hsite]
          exact h.2.2.1 k hkp
        rw [candidateSweepFrame ring S
          (PPL.shiftRight ring root p) i he hd]
        exact hbefore

/-- The full dynamic inductive step, with no restriction on which
birth-free edge the scheduler chooses. The service either retains
a distinguished bullet at some offset or witnesses the actual
absorption with all candidates return-compatible. -/
theorem candidateSweepStep {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → NativeCand)
    (p : Nat) (e : Fin n)
    (h : CandidateSweepState ring root S p) :
    (∃ q : Nat, CandidateSweepState ring root
      (birthFreeCandidateStep ring S e) q) ∨
      CandidateSweepAbsorbed ring root
        (birthFreeCandidateStep ring S e) := by
  by_cases he : e = PPL.shiftRight ring root p
  · rw [he]
    by_cases hnext : p + 1 < n
    · exact Or.inl ⟨p + 1,
        candidateSweepInteriorStep hn ring root S p h hnext⟩
    · have hlast : p + 1 = n := by
        have hp := h.2.1.1
        omega
      exact Or.inr
        (candidateSweepFinalStep hn ring root S p h hlast)
  · exact Or.inl ⟨p,
      candidateSweepNonHostStep hn ring root S p e h he⟩

/-! A phase cursor stores the actual distinguished bullet offset.
n is terminal. The native/candidate map remains the production Phi_e
until terminal; after terminal we freeze this analytical state.
The stop is by phase, not by an earlier native absorption lookalike. -/

abbrev CandidateSweepCursorState (n : Nat) :=
  (Fin n → NativeCand) × Nat

def candidateSweepCursorStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : CandidateSweepCursorState n) (e : Fin n) :
    CandidateSweepCursorState n :=
  if z.2 < n then
    (birthFreeCandidateStep ring z.1 e,
      if e = PPL.shiftRight ring root z.2
      then z.2 + 1 else z.2)
  else z

def CandidateSweepCursorDone {n : Nat}
    (z : CandidateSweepCursorState n) : Prop :=
  n ≤ z.2

def CandidateSweepCursorGood {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : CandidateSweepCursorState n) : Prop :=
  (z.2 < n ∧ CandidateSweepState ring root z.1 z.2) ∨
  (z.2 = n ∧ CandidateSweepAbsorbed ring root z.1)

theorem candidateSweepCursorDoneAbsorbed {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : CandidateSweepCursorState n)
    (hgood : CandidateSweepCursorGood ring root z)
    (hdone : CandidateSweepCursorDone z) :
    CandidateSweepAbsorbed ring root z.1 := by
  rcases hgood with hactive | hfinal
  · have hc : z.2 < n := hactive.1
    have hd : n ≤ z.2 := hdone
    exact False.elim (by omega : False)
  · exact hfinal.2

/-- Every edge preserves the phase-indexed candidate sweep.
This includes the terminating nominated service. -/
theorem candidateSweepCursorGoodStep {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (z : CandidateSweepCursorState n)
    (e : Fin n)
    (hgood : CandidateSweepCursorGood ring root z) :
    CandidateSweepCursorGood ring root
      (candidateSweepCursorStep ring root z e) := by
  by_cases hc : z.2 < n
  · have hstate : CandidateSweepState ring root z.1 z.2 := by
      rcases hgood with hactive | hfinal
      · exact hactive.2
      · have heq : z.2 = n := hfinal.1
        exact False.elim (by omega : False)
    by_cases he : e = PPL.shiftRight ring root z.2
    · by_cases hnext : z.2 + 1 < n
      · have hs := candidateSweepInteriorStep
          hn ring root z.1 z.2 hstate hnext
        have hnew : CandidateSweepCursorGood ring root
            (birthFreeCandidateStep ring z.1 e, z.2 + 1) := by
          rw [he]
          exact Or.inl ⟨hnext, hs⟩
        simpa only [candidateSweepCursorStep,
          if_pos hc, if_pos he] using hnew
      · have hlast : z.2 + 1 = n := by omega
        have hs := candidateSweepFinalStep
          hn ring root z.1 z.2 hstate hlast
        have hnew : CandidateSweepCursorGood ring root
            (birthFreeCandidateStep ring z.1 e, z.2 + 1) := by
          rw [he]
          exact Or.inr ⟨hlast, hs⟩
        simpa only [candidateSweepCursorStep,
          if_pos hc, if_pos he] using hnew
    · have hs := candidateSweepNonHostStep
        hn ring root z.1 z.2 e hstate he
      have hnew : CandidateSweepCursorGood ring root
          (birthFreeCandidateStep ring z.1 e, z.2) :=
        Or.inl ⟨hc, hs⟩
      simpa only [candidateSweepCursorStep,
        if_pos hc, if_neg he] using hnew
  · have hsame :
        candidateSweepCursorStep ring root z e = z := by
      simp only [candidateSweepCursorStep, if_neg hc]
    rw [hsame]
    exact hgood

/-- The projected component is exactly the real Phi_e on every
nonterminal cursor service, and only there. -/
theorem candidateSweepCursorNativeStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : CandidateSweepCursorState n) (e : Fin n)
    (h : z.2 < n) :
    (candidateSweepCursorStep ring root z e).1 =
      birthFreeCandidateStep ring z.1 e := by
  simp only [candidateSweepCursorStep, if_pos h]

theorem candidateSweepCursorDrop {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : CandidateSweepCursorState n)
    (h : ¬ CandidateSweepCursorDone z) :
    n - (candidateSweepCursorStep ring root z
      (PPL.shiftRight ring root z.2)).2 + 1 ≤
      n - z.2 := by
  have hc : z.2 < n := by
    change ¬ n ≤ z.2 at h
    omega
  simp only [candidateSweepCursorStep, if_pos hc, ↓reduceIte]
  omega

theorem candidateSweepCursorNonincrease {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : CandidateSweepCursorState n)
    (_h : ¬ CandidateSweepCursorDone z) (e : Fin n) :
    n - (candidateSweepCursorStep ring root z e).2 ≤
      n - z.2 := by
  by_cases hc : z.2 < n
  · by_cases he : e = PPL.shiftRight ring root z.2
    · simp only [candidateSweepCursorStep,
        if_pos hc, if_pos he]
      omega
    · simp only [candidateSweepCursorStep,
        if_pos hc, if_neg he]
      omega
  · simp only [candidateSweepCursorStep, if_neg hc]
    omega

/-- Exact finite-horizon n(n-p) expected-interaction reserve
for the phase cursor. No native-lookalike early stopping. -/
theorem candidateSweepCursorClockCost {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : CandidateSweepCursorState n) (T : Nat) :
    costNumerator (candidateSweepCursorStep ring root)
      CandidateSweepCursorDone z T ≤
      n ^ T * (n * (n - z.2)) := by
  exact Prob.costNumerator_le_of_nominated_edge
    (candidateSweepCursorStep ring root)
    CandidateSweepCursorDone
    (fun x : CandidateSweepCursorState n => n - x.2)
    (fun x : CandidateSweepCursorState n =>
      PPL.shiftRight ring root x.2)
    (candidateSweepCursorDrop ring root)
    (candidateSweepCursorNonincrease ring root)
    z T

/-- Pathwise phase correctness: once the cursor reaches n its
actual projected component is a genuine candidate-swept
absorption. The same stopping numerator is bounded by the
explicit cursor's numerator. -/
theorem candidateSweepAbsorbedCostLeClock {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) :
    ∀ T (z : CandidateSweepCursorState n),
      CandidateSweepCursorGood ring root z →
      costNumerator (birthFreeCandidateStep ring)
        (CandidateSweepAbsorbed ring root) z.1 T ≤
      costNumerator (candidateSweepCursorStep ring root)
        CandidateSweepCursorDone z T := by
  classical
  intro T
  induction T with
  | zero =>
      intro z _
      simp only [costNumerator_zero]
      exact Nat.le_refl 0
  | succ T ih =>
      intro z hgood
      by_cases ha : CandidateSweepAbsorbed ring root z.1
      · rw [costNumerator_terminal (birthFreeCandidateStep ring)
          (CandidateSweepAbsorbed ring root) z.1 ha (T + 1)]
        exact Nat.zero_le _
      · have hd : ¬ CandidateSweepCursorDone z := by
          intro hdone
          exact ha (candidateSweepCursorDoneAbsorbed
            ring root z hgood hdone)
        have hc : z.2 < n := by
          change ¬ n ≤ z.2 at hd
          omega
        rw [costNumerator_succ (birthFreeCandidateStep ring)
          (CandidateSweepAbsorbed ring root) z.1 ha T,
          costNumerator_succ (candidateSweepCursorStep ring root)
            CandidateSweepCursorDone z hd T]
        have hchildren := ofFn_sum_le
          (fun e : Fin n =>
            costNumerator (birthFreeCandidateStep ring)
              (CandidateSweepAbsorbed ring root)
              (birthFreeCandidateStep ring z.1 e) T)
          (fun e : Fin n =>
            costNumerator (candidateSweepCursorStep ring root)
              CandidateSweepCursorDone
              (candidateSweepCursorStep ring root z e) T)
          (fun e => by
            have hh := ih (candidateSweepCursorStep ring root z e)
              (candidateSweepCursorGoodStep hn ring root z e hgood)
            have hproj := candidateSweepCursorNativeStep
              ring root z e hc
            rw [hproj] at hh
            exact hh)
        exact Nat.add_le_add_left hchildren _

/-- From ANY genuine distinguished-bullet host at offset p, its
first absorption with all candidates swept has finite-horizon
cost at most n(n-p) and hence n squared. -/
theorem candidateSweepAbsorptionCost {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → NativeCand)
    (p : Nat) (h : CandidateSweepState ring root S p)
    (T : Nat) :
    costNumerator (birthFreeCandidateStep ring)
      (CandidateSweepAbsorbed ring root) S T ≤
      n ^ T * n ^ 2 := by
  have hgood : CandidateSweepCursorGood ring root (S, p) :=
    Or.inl ⟨h.2.1.1, h⟩
  have hcompare := candidateSweepAbsorbedCostLeClock
    hn ring root T (S, p) hgood
  have hclock := candidateSweepCursorClockCost ring root
    (S, p) T
  have hb : n * (n - p) ≤ n ^ 2 := by
    calc
      n * (n - p) ≤ n * n :=
        Nat.mul_le_mul_left n (Nat.sub_le n p)
      _ = n ^ 2 := by rw [Nat.pow_two]
  exact Nat.le_trans (Nat.le_trans hcompare hclock)
    (Nat.mul_le_mul_left (n ^ T) hb)

/-- Native completion after an actual swept absorption is
precisely the old return stage. This new forward theorem
discharges the previously missing ReturnCandSite premise. -/
theorem candidateSweepAbsorptionReturnDoubledCost {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → NativeCand)
    (h : CandidateSweepAbsorbed ring root S) (T : Nat) :
    2 * costNumerator (birthFreeCandidateStep ring)
      (CandidateReturnTarget root) S T ≤
        n ^ T * (2 * n ^ 2) := by
  exact candidateAbsorbedReturnDoubledCost
    hn ring root S h.1 h.2 T

end ReferencePreparationTrail
end L3


/-!
First genuine incident firing and the sharp six-stage
candidate-preparation clock.
-/

namespace L3
namespace ReferencePreparationTrail

open ReferencePreparationCandidate
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

def CandidateReadyCut {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → NativeCand) : Prop :=
  ReadyCut ring root (candidateNative S)

def CandidateFiredSweep {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → NativeCand) : Prop :=
  ∃ p : Nat, CandidateSweepState ring root S p

/-- At an outgoing ready edge the root SAN-clears its old record,
and an occupied follower one gets genuine first credit. This
requires no initial restriction on the candidate record. -/
theorem candidateReadyOutgoingSweep {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → NativeCand)
    (h : CandidateReadyCut ring root S) :
    CandidateSweepState ring root
      (birthFreeCandidateStep ring S root) 1 := by
  have hne := rightNe hn ring root
  have hproj :
      candidateNative (birthFreeCandidateStep ring S root) =
        nativeE ring (candidateNative S) root :=
    birthFreeCandidateStep_native (by omega : 2 ≤ n) ring S root
  have hnext := rootedStep hn ring root
    (candidateNative S) root h.1
  have hfresh := freshOutgoing hn ring root
    (candidateNative S) h
  have hpair := sealed_prep_actual_old_pair ring
    (candidateNative S) root hne
  have hy : (S (ring.rightNeighbor root)).native.l = false :=
    follower (candidateNative S) root
      (ring.rightNeighbor root) h.1.2.1 hne
  have hout : 0 < outBullet (S root).native := by
    have h1 : (S root).native.l = true := h.1.1
    have h2 : (S root).native.sg = true := h.2.2
    simp [outBullet, h1, h2]
  have hl :
      (certLiteralEPair (S root).native
        (S (ring.rightNeighbor root)).native).2.l = false := by
    have hh := follower
      (nativeE ring (candidateNative S) root)
      root (ring.rightNeighbor root) hnext.2.1 hne
    rw [hpair.2] at hh
    exact hh
  have hb :
      (certLiteralEPair (S root).native
        (S (ring.rightNeighbor root)).native).2.b ≠
          (0 : Fin 3) := by
    have hh0 := hfresh.2
    rw [shiftOne, hpair.2] at hh0
    have hh : (certLiteralEPair (S root).native
        (S (ring.rightNeighbor root)).native).2.b = (2 : Fin 3) := hh0
    intro hz
    rw [hz] at hh
    have hbad : (0 : Fin 3) ≠ (2 : Fin 3) := by decide
    exact hbad hh
  have hs :
      (certLiteralEPair (S root).native
        (S (ring.rightNeighbor root)).native).2.sg = false := by
    have hh := hfresh.1.2.2.2 1 (Nat.le_refl 1)
    rw [shiftOne, hpair.2] at hh
    exact hh
  have hrootSite :
      ReturnCandSite (birthFreeCandidateStep ring S root root) :=
    candidateSweepRootSan hn ring root S root
      hnext.1 (Or.inl rfl)
  have hhost :
      CandidateSweepHost
        (birthFreeCandidateStep ring S root
          (PPL.shiftRight ring root 1)) := by
    have hh := candidateSweepEntry
      (S root) (S (ring.rightNeighbor root))
      hy hout hl hb hs
    rw [shiftOne]
    simpa [birthFreeCandidateStep, hne] using hh
  refine ⟨?_, ?_, ?_, hhost⟩
  · rw [hproj]
    exact hnext
  · rw [hproj]
    exact hfresh.1
  · intro k hk
    have hzero : k = 0 := by omega
    rw [hzero, referencePreparationShiftZero]
    exact hrootSite

/-- The incoming incident service creates the dummy at the
leader, its SAN-zero record being the first sweep host. -/
theorem candidateReadyIncomingSweep {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root e : Fin n) (S : Fin n → NativeCand)
    (h : CandidateReadyCut ring root S)
    (hj : ring.rightNeighbor e = root) :
    CandidateSweepState ring root
      (birthFreeCandidateStep ring S e) 0 := by
  have hproj :
      candidateNative (birthFreeCandidateStep ring S e) =
        nativeE ring (candidateNative S) e :=
    birthFreeCandidateStep_native (by omega : 2 ≤ n) ring S e
  have hnext := rootedStep hn ring root
    (candidateNative S) e h.1
  have hfresh := freshIncoming hn ring root e
    (candidateNative S) h hj
  have hrootSite :
      ReturnCandSite (birthFreeCandidateStep ring S e root) :=
    candidateSweepRootSan hn ring root S e
      hnext.1 (Or.inr hj)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hproj]
    exact hnext
  · rw [hproj]
    exact hfresh.1
  · intro k hk
    exact False.elim (by omega : False)
  · rw [referencePreparationShiftZero]
    exact candidateReturnHost
      (birthFreeCandidateStep ring S e root) hrootSite

theorem candidateReadyNonincident {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → NativeCand)
    (e : Fin n) (h : CandidateReadyCut ring root S)
    (he : e ≠ root) (hj : ring.rightNeighbor e ≠ root) :
    CandidateReadyCut ring root
      (birthFreeCandidateStep ring S e) := by
  have hp := birthFreeCandidateStep_native
    (by omega : 2 ≤ n) ring S e
  rw [CandidateReadyCut, hp]
  exact readyNonincident hn ring root
    (candidateNative S) e h he hj

/-- Compare the real Phi_e candidate first-firing cut with the
same original two-port IID incident clock, allowing every
intervening nonincident service to execute normally. -/
theorem candidateReadyCostLeIncident {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) :
    ∀ T (S : Fin n → NativeCand),
      CandidateReadyCut ring root S →
      costNumerator (birthFreeCandidateStep ring)
        (CandidateFiredSweep ring root) S T ≤
      costNumerator (referencePreparationIncidentNativeStep ring root)
        (fun z : Bool × TripleNativeState n => z.1 = true)
        (false, candidateNative S) T := by
  classical
  intro T
  induction T with
  | zero =>
      intro S _
      simp only [costNumerator_zero]
      exact Nat.le_refl 0
  | succ T ih =>
      intro S hready
      by_cases hf : CandidateFiredSweep ring root S
      · rw [costNumerator_terminal
          (birthFreeCandidateStep ring)
          (CandidateFiredSweep ring root) S hf (T + 1)]
        exact Nat.zero_le _
      · have hflag :
          ¬ (fun z : Bool × TripleNativeState n =>
            z.1 = true) (false, candidateNative S) := by
          intro h
          cases h
        rw [costNumerator_succ (birthFreeCandidateStep ring)
            (CandidateFiredSweep ring root) S hf T,
          costNumerator_succ
            (referencePreparationIncidentNativeStep ring root)
            (fun z : Bool × TripleNativeState n => z.1 = true)
            (false, candidateNative S) hflag T]
        apply Nat.add_le_add_left
        apply ofFn_sum_le
        intro e
        by_cases he : e = root
        · have hfire :
            CandidateFiredSweep ring root
              (birthFreeCandidateStep ring S e) := by
            rw [he]
            exact ⟨1, candidateReadyOutgoingSweep
              hn ring root S hready⟩
          rw [costNumerator_terminal
            (birthFreeCandidateStep ring)
            (CandidateFiredSweep ring root)
            (birthFreeCandidateStep ring S e) hfire T]
          exact Nat.zero_le _
        · by_cases hb : e = ring.leftNeighbor root
          · have hj : ring.rightNeighbor e = root := by
              rw [hb, rightLeft]
            have hfire :
                CandidateFiredSweep ring root
                  (birthFreeCandidateStep ring S e) :=
              ⟨0, candidateReadyIncomingSweep
                hn ring root e S hready hj⟩
            rw [costNumerator_terminal
              (birthFreeCandidateStep ring)
              (CandidateFiredSweep ring root)
              (birthFreeCandidateStep ring S e) hfire T]
            exact Nat.zero_le _
          · have hj : ring.rightNeighbor e ≠ root := by
              intro hroot
              have hh :
                  ring.rightNeighbor e =
                    ring.rightNeighbor (ring.leftNeighbor root) :=
                hroot.trans (rightLeft ring root).symm
              exact hb (referencePreparationRightInjective ring hh)
            have hnext := candidateReadyNonincident hn ring
              root S e hready he hj
            have hchild := ih (birthFreeCandidateStep ring S e)
              hnext
            rw [birthFreeCandidateStep_native
              (by omega : 2 ≤ n) ring S e] at hchild
            simpa only [referencePreparationIncidentNativeStep,
              referencePreparationIncidentFlagStep,
              if_neg he, if_neg hb] using hchild

theorem candidateReadyHalfCost {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → NativeCand)
    (h : CandidateReadyCut ring root S) (T : Nat) :
    2 * costNumerator (birthFreeCandidateStep ring)
      (CandidateFiredSweep ring root) S T ≤ n ^ T * n := by
  have hc := candidateReadyCostLeIncident hn ring root T S h
  exact Nat.le_trans (Nat.mul_le_mul_left 2 hc)
    (referencePreparationIncidentNativeHalfCost hn
      ring root (candidateNative S) T)

/-- The forward cursor authenticates the absorption, and the
candidate return rule clears all records. The phases use the
same birth-free candidate map without invented interactions. -/
theorem candidateFiredReturnDoubledCost {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → NativeCand)
    (h : CandidateFiredSweep ring root S) (T : Nat) :
    2 * costNumerator (birthFreeCandidateStep ring)
      (CandidateReturnTarget root) S T ≤
        n ^ T * (4 * n ^ 2) := by
  obtain ⟨p, hp⟩ := h
  have hfirst : ∀ U,
      2 * costNumerator (birthFreeCandidateStep ring)
        (fun x => CandidateSweepAbsorbed ring root x ∨
          CandidateReturnTarget root x) S U ≤
      n ^ U * (2 * n ^ 2) := by
    intro U
    have hmono := Prob.costNumerator_target_mono
      (birthFreeCandidateStep ring)
      (CandidateSweepAbsorbed ring root)
      (fun x => CandidateSweepAbsorbed ring root x ∨
        CandidateReturnTarget root x)
      (by intro x hx; exact Or.inl hx) S U
    have hc := candidateSweepAbsorptionCost
      hn ring root S p hp U
    calc
      2 * costNumerator (birthFreeCandidateStep ring)
          (fun x => CandidateSweepAbsorbed ring root x ∨
            CandidateReturnTarget root x) S U ≤
        2 * costNumerator (birthFreeCandidateStep ring)
          (CandidateSweepAbsorbed ring root) S U :=
        Nat.mul_le_mul_left 2 hmono
      _ ≤ 2 * (n ^ U * n ^ 2) :=
        Nat.mul_le_mul_left 2 hc
      _ = n ^ U * (2 * n ^ 2) := by ac_rfl
  have hsecond : ∀ z,
      CandidateSweepAbsorbed ring root z → ∀ U,
      2 * costNumerator (birthFreeCandidateStep ring)
        (CandidateReturnTarget root) z U ≤
      n ^ U * (2 * n ^ 2) := by
    intro z hz U
    exact candidateSweepAbsorptionReturnDoubledCost
      hn ring root z hz U
  have hc := doubledStageCost
    (birthFreeCandidateStep ring) S
    (CandidateSweepAbsorbed ring root)
    (CandidateReturnTarget root)
    (2 * n ^ 2) (2 * n ^ 2)
    hfirst hsecond T
  exact Nat.le_trans hc
    (Nat.mul_le_mul_left (n ^ T)
      (by omega :
        2 * n ^ 2 + 2 * n ^ 2 ≤ 4 * n ^ 2))

/-- The n/2 incident, n^2 distinguished sweep, and n^2
return are composed only once after genuine readiness. -/
theorem candidateReadyReturnDoubledCost {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → NativeCand)
    (h : CandidateReadyCut ring root S) (T : Nat) :
    2 * costNumerator (birthFreeCandidateStep ring)
      (CandidateReturnTarget root) S T ≤
      n ^ T * (4 * n ^ 2 + n) := by
  have hfirst : ∀ U,
      2 * costNumerator (birthFreeCandidateStep ring)
        (fun x => CandidateFiredSweep ring root x ∨
          CandidateReturnTarget root x) S U ≤
      n ^ U * n := by
    intro U
    have hmono := Prob.costNumerator_target_mono
      (birthFreeCandidateStep ring)
      (CandidateFiredSweep ring root)
      (fun x => CandidateFiredSweep ring root x ∨
        CandidateReturnTarget root x)
      (by intro x hx; exact Or.inl hx) S U
    exact Nat.le_trans (Nat.mul_le_mul_left 2 hmono)
      (candidateReadyHalfCost hn ring root S h U)
  have hsecond : ∀ z,
      CandidateFiredSweep ring root z → ∀ U,
      2 * costNumerator (birthFreeCandidateStep ring)
        (CandidateReturnTarget root) z U ≤
      n ^ U * (4 * n ^ 2) := by
    intro z hz U
    exact candidateFiredReturnDoubledCost
      hn ring root z hz U
  have hc := doubledStageCost
    (birthFreeCandidateStep ring) S
    (CandidateFiredSweep ring root)
    (CandidateReturnTarget root)
    n (4 * n ^ 2) hfirst hsecond T
  exact Nat.le_trans hc
    (Nat.mul_le_mul_left (n ^ T)
      (by omega : n + 4 * n ^ 2 ≤ 4 * n ^ 2 + n))

/-- Unrestricted native/candidate finite-horizon projection
identity, proved by direct recursion rather than unfolding a
HeadlineConfiguration into a function. -/
theorem candidateNativeCostEq {n : Nat}
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (P : TripleNativeState n → Prop) :
    ∀ T (S : Fin n → NativeCand),
      costNumerator (birthFreeCandidateStep ring)
        (fun x => P (candidateNative x)) S T =
      costNumerator (nativeE ring) P
        (candidateNative S) T := by
  classical
  intro T
  induction T with
  | zero =>
      intro S
      simp only [costNumerator_zero]
  | succ T ih =>
      intro S
      by_cases hp : P (candidateNative S)
      · rw [costNumerator_terminal
          (birthFreeCandidateStep ring)
          (fun x => P (candidateNative x)) S hp (T + 1),
          costNumerator_terminal
            (nativeE ring) P (candidateNative S) hp (T + 1)]
      · rw [costNumerator_succ
          (birthFreeCandidateStep ring)
          (fun x => P (candidateNative x)) S hp T,
          costNumerator_succ
            (nativeE ring) P (candidateNative S) hp T]
        congr 1
        exact ofFn_sum_eq _ _ (fun e => by
          have hh := ih (birthFreeCandidateStep ring S e)
          rw [birthFreeCandidateStep_native hn ring S e] at hh
          exact hh)

theorem candidateFirstReadyCost {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → NativeCand)
    (hroot : Rooted ring root (candidateNative S))
    (T : Nat) :
    costNumerator (birthFreeCandidateStep ring)
      (CandidateReadyCut ring root) S T ≤
      n ^ T * (3 * n ^ 2) := by
  have hh := candidateNativeCostEq
    (by omega : 2 ≤ n) ring
    (ReadyCut ring root) T S
  change costNumerator (birthFreeCandidateStep ring)
    (CandidateReadyCut ring root) S T =
    costNumerator (nativeE ring) (ReadyCut ring root)
      (candidateNative S) T at hh
  rw [hh]
  exact firstThreeStagesCost hn ring root
    (candidateNative S) hroot T

/-- Full six-stage expected-time coefficient for
candidate-zero native preparation on ONE birth-free projected
state space. This is the FIRST fully prepared hit, not the
premature first native-only hit refuted earlier. The
sweep phase is authenticated by CandidateSweepCursorState. -/
theorem candidateSingletonPreparationDoubledCost {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → NativeCand)
    (hroot : Rooted ring root (candidateNative S))
    (T : Nat) :
    2 * costNumerator (birthFreeCandidateStep ring)
      (CandidateReturnTarget root) S T ≤
        n ^ T * (10 * n ^ 2 + n) := by
  have hfirst : ∀ U,
      2 * costNumerator (birthFreeCandidateStep ring)
        (fun x => CandidateReadyCut ring root x ∨
          CandidateReturnTarget root x) S U ≤
      n ^ U * (6 * n ^ 2) := by
    intro U
    have hmono := Prob.costNumerator_target_mono
      (birthFreeCandidateStep ring)
      (CandidateReadyCut ring root)
      (fun x => CandidateReadyCut ring root x ∨
        CandidateReturnTarget root x)
      (by intro x hx; exact Or.inl hx) S U
    have hc := candidateFirstReadyCost hn
      ring root S hroot U
    calc
      2 * costNumerator (birthFreeCandidateStep ring)
          (fun x => CandidateReadyCut ring root x ∨
            CandidateReturnTarget root x) S U ≤
        2 * costNumerator (birthFreeCandidateStep ring)
          (CandidateReadyCut ring root) S U :=
        Nat.mul_le_mul_left 2 hmono
      _ ≤ 2 * (n ^ U * (3 * n ^ 2)) :=
        Nat.mul_le_mul_left 2 hc
      _ = n ^ U * (6 * n ^ 2) := by
        rw [Nat.mul_left_comm 2 (n ^ U), ← Nat.mul_assoc 2 3]
  have hsecond : ∀ z,
      CandidateReadyCut ring root z → ∀ U,
      2 * costNumerator (birthFreeCandidateStep ring)
        (CandidateReturnTarget root) z U ≤
      n ^ U * (4 * n ^ 2 + n) := by
    intro z hz U
    exact candidateReadyReturnDoubledCost
      hn ring root z hz U
  have hc := doubledStageCost
    (birthFreeCandidateStep ring) S
    (CandidateReadyCut ring root)
    (CandidateReturnTarget root)
    (6 * n ^ 2) (4 * n ^ 2 + n)
    hfirst hsecond T
  exact Nat.le_trans hc
    (Nat.mul_le_mul_left (n ^ T)
      (by omega :
        6 * n ^ 2 + (4 * n ^ 2 + n) ≤ 10 * n ^ 2 + n))

/-- Explicit H_cand specialization; the candidate ledger theorem
is actually stronger and holds for arbitrary legal CPriv fields. -/
theorem candidateGeneratedSingletonDoubledCost {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (S : Fin n → NativeCand)
    (hroot : Rooted ring root (candidateNative S))
    (_hgenerated : H_cand ring S) (T : Nat) :
    2 * costNumerator (birthFreeCandidateStep ring)
      (CandidateReturnTarget root) S T ≤
        n ^ T * (10 * n ^ 2 + n) := by
  exact candidateSingletonPreparationDoubledCost
    hn ring root S hroot T

/-- The same endpoint transported along the REAL physical
no-FIRE word, with no change of unrelated protocol fields.
Grant-free and clean-native facts at the cut remain explicit. -/
theorem candidatePreparedPhysicalWordHandoff {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (C : HeadlineConfiguration n)
    (edges : List (Fin n))
    (hword : NativeLiftNoFireWord ring C edges)
    (htarget : CandidateReturnTarget root
      (candidateWord ring (physicalCandidates C) edges))
    (hprotected : Protected ring
      (nativeProjection (nativeLiftRealRun ring C edges)))
    (hgrant : NativeLiftGrantFree
      (nativeLiftRealRun ring C edges))
    (hclean : C_native ring
      (nativeProjection (nativeLiftRealRun ring C edges))) :
    ReferencePreparationPreparedCore ring
      (nativeLiftRealRun ring C edges) := by
  have hp := noFirePhysicalWord hn ring C edges hword
  rw [← hp] at htarget
  have hnativ : ReferencePreparationNativePreparedAt root
      (nativeProjection (nativeLiftRealRun ring C edges)) :=
    htarget.1
  have hcand : EmptyCandidates
      (physicalCandidates (nativeLiftRealRun ring C edges)) :=
    htarget.2
  exact nativePreparedPhysicalCandidateHandoff ring root
    (nativeLiftRealRun ring C edges)
    hnativ hprotected hgrant hclean hcand

end ReferencePreparationTrail
end L3

