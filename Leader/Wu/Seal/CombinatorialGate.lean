import Leader.Wu.Seal.ABGate

/-!
# Audit brick for the combinatorial Ready-or-AB gate

This file records the local facts needed to audit the Stage II argument against the
repository's actual four-state convention:

* `A = (home, front) = 11`,
* `B = 10`,
* `C = 00`, and
* `D = 01`.

Thus the particle followed by the proposed tagged-gap argument is the actual
front bit, occupied on `A,D`.  It is not XNOR of the two displayed bits.
Correcting that terminology does not alter the abstract transition rows:
away from exact Ready or exact `A B`, fronts execute cyclic `10 -> 01` TASEP.

The main new local lemma verifies the delicate Stage-II assertion: once a
tagged front edge is enabled, scheduling any different edge cannot disable it
before the Ready-or-AB gate.  The remaining lemmas record pointwise home
stability, the exact `D B -> C A` bridge, the following rear hop into `C`, and
the fact that `A C` is the only local row through which the target `A` can
escape without already being a gate.

No sextic hitting estimate is asserted here.  Its remaining content is the
stopped tagged-gap/reflected-queue counting and renewal argument, not another
four-state projection claim.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepCombinatorialGateAuditSol

open PPLL PPLLResearchFormulation PPLLTraceConvergence
open PPLLSchedulerBlocks PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepHomeFrontQuotientSol
open PPartialSealSweepHomeTrapCurrentSol
open PPartialSealSweepABReadyCompositionSol
open PPartialSealSweepABGateBreakthroughSol
open PPartialSealSweepReadySuffixHalfMassSol

set_option autoImplicit false

variable {n : Nat}

def actualA : SealSweepHomeFrontSite := (true, true)
def actualB : SealSweepHomeFrontSite := (true, false)
def actualC : SealSweepHomeFrontSite := (false, false)
def actualD : SealSweepHomeFrontSite := (false, true)

/-- XNOR is the wrong particle bit for the actual source convention. -/
def homeFrontXnorBit (q : SealSweepHomeFrontSite) : Bool :=
  decide (q.1 = q.2)

/-- The corrected `C,D` values exhibit both directions of the terminology
error: XNOR occupies `C` but not `D`, whereas the actual front occupies `D`
but not `C`. -/
theorem homeFrontXnor_differs_from_front_on_C_D :
    homeFrontXnorBit actualC = true /\ actualC.2 = false /\
      homeFrontXnorBit actualD = false /\ actualD.2 = true := by
  decide

/-- Exact physical quotient rows under the corrected `C=00,D=01` mapping. -/
theorem corrected_sealSweep_transition_table :
    sealSweepHomeFrontPair actualA actualA = (actualA, actualC) /\
    sealSweepHomeFrontPair actualD actualA = (actualC, actualD) /\
    sealSweepHomeFrontPair actualA actualC = (actualB, actualD) /\
    sealSweepHomeFrontPair actualD actualC = (actualC, actualD) /\
    sealSweepHomeFrontPair actualD actualB = (actualC, actualA) := by
  decide

/-- A directed front `10` edge in a Boolean front configuration. -/
def Front10At (ring : DirectedRing n) (F : Fin n -> Bool)
    (edge : Fin n) : Prop :=
  F edge = true /\ F (ring.rightNeighbor edge) = false

/-- Scheduling another edge cannot disable an already enabled clockwise TASEP
front.  The only overlapping incoming update sees the tagged site occupied;
the only overlapping outgoing update sees its successor empty. -/
theorem clockwiseTasep_front10At_localStep_of_ne
    (ring : DirectedRing n) (F : Fin n -> Bool)
    (edge scheduled : Fin n)
    (h10 : Front10At ring F edge) (hne : scheduled ≠ edge) :
    Front10At ring
      (localStep ring clockwiseTasepPair F scheduled) edge := by
  let j := ring.rightNeighbor scheduled
  constructor
  · by_cases hej : edge = j
    · have hjTrue : F j = true := by simpa [hej] using h10.1
      have hes : edge ≠ scheduled := hne.symm
      have hjs : j ≠ scheduled := by
        intro h
        exact hes (hej.trans h)
      simp [localStep, j, hes, hej, hjs, clockwiseTasepPair, hjTrue]
    · have hes : edge ≠ scheduled := hne.symm
      simp [localStep, j, hes, hej, h10.1]
  · let out := ring.rightNeighbor edge
    have houtj : out ≠ j := by
      intro houtj
      have heq : edge = scheduled :=
        rightNeighbor_injective ring houtj
      exact hne heq.symm
    by_cases houts : out = scheduled
    · have hsFalse : F scheduled = false := by
        rw [← houts]
        exact h10.2
      simp [localStep, j, out, houts, houtj,
        clockwiseTasepPair, hsFalse]
    · simp [localStep, j, out, houts, houtj, h10.2]

/-- A front `10` edge in the exact quotient. -/
def HomeFrontFront10At (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) (edge : Fin n) : Prop :=
  Front10At ring (homeFrontFrontProjection X) edge

/-- Stage II's local persistence assertion, now stated against the
actual quotient: before `Ready or AB`, every scheduler edge other than the
tagged front edge preserves its enabled-front status. -/
theorem homeFrontFront10At_localStep_of_ne_of_not_gate
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite)
    (edge scheduled : Fin n)
    (hnotGate : ¬ HomeFrontReadyOrAB ring X)
    (h10 : HomeFrontFront10At ring X edge)
    (hne : scheduled ≠ edge) :
    HomeFrontFront10At ring
      (localStep ring sealSweepHomeFrontPair X scheduled) edge := by
  unfold HomeFrontFront10At at h10 ⊢
  rw [homeFrontFrontProjection_localStep_eq_tasep_of_not_gate
    ring X scheduled hnotGate]
  exact clockwiseTasep_front10At_localStep_of_ne
    ring (homeFrontFrontProjection X) edge scheduled h10 hne

/-- The chosen next physical home is stable through every gate-free local
step; in fact all home sites are stable pointwise. -/
theorem homeFront_homeBit_localStep_eq_of_not_gate
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite)
    (scheduled site : Fin n)
    (hnotGate : ¬ HomeFrontReadyOrAB ring X) :
    (localStep ring sealSweepHomeFrontPair X scheduled site).1 =
      (X site).1 := by
  exact congrFun
    (homeFrontHomeProjection_localStep_eq_of_not_gate
      ring X scheduled hnotGate) site

/-- The exact bridge interaction at the target home. -/
theorem corrected_DB_transition :
    sealSweepHomeFrontPair actualD actualB = (actualC, actualA) := by
  rfl

/-- After `D B -> C A`, either possible rear front (`A` or `D`) hops into
the new `C`; its output at that site is a `D` front, immediately exposing the
exact Ready pair `D A`. -/
theorem corrected_DB_then_rearHop_exposes_ready
    (rear : SealSweepHomeFrontSite) (hrear : rear.2 = true) :
    sealSweepFrontHitsHomePair
      (sealSweepHomeFrontPair rear actualC).2 actualA = true := by
  rcases rear with ⟨home, front⟩
  cases home <;> cases front <;>
    simp [actualA, actualC, sealSweepHomeFrontPair,
      sealSweepFrontHitsHomePair] at hrear ⊢

/-- From a target `A`, the left output changes only on the harmful outgoing
`A C` hop.  The other three right letters either already form Ready/AB or
stutter at the target. -/
theorem corrected_targetA_changes_iff_rightC
    (right : SealSweepHomeFrontSite) :
    (sealSweepHomeFrontPair actualA right).1 ≠ actualA <->
      right = actualC := by
  rcases right with ⟨home, front⟩
  cases home <;> cases front <;>
    decide

/-! ## The first stochastic residual: exact finite scheduler races -/

/-- Did `front` occur before `rear` in a finite scheduler word?  Words that
contain neither distinguished edge return `false`; they are deliberately not
assigned to either winner. -/
def firstRelevantFrontWins (front rear : Fin n) : DetSchedule n → Bool
  | [] => false
  | edge :: rest =>
      if edge = front then true
      else if edge = rear then false
      else firstRelevantFrontWins front rear rest

/-- The existing first-relevant-clock involution exchanges the two race
outcomes pointwise. -/
theorem firstRelevantFrontWins_swap
    (front rear : Fin n) (hne : front ≠ rear)
    (word : DetSchedule n) :
    firstRelevantFrontWins front rear
        (homeFrontReadySuffixSwap front rear word) =
      firstRelevantFrontWins rear front word := by
  induction word with
  | nil => rfl
  | cons edge rest ih =>
      by_cases hef : edge = front
      · subst edge
        simp [firstRelevantFrontWins, homeFrontReadySuffixSwap,
          hne, hne.symm]
      · by_cases her : edge = rear
        · subst edge
          simp [firstRelevantFrontWins, homeFrontReadySuffixSwap,
            hne, hne.symm]
        · simp [firstRelevantFrontWins, homeFrontReadySuffixSwap,
            hef, her, ih]

private theorem audit_nodup_filter_of_nodup
    {alpha : Type} (p : alpha → Bool) (xs : List alpha)
    (hxs : xs.Nodup) :
    (xs.filter p).Nodup := by
  rw [List.nodup_iff_pairwise_ne] at hxs ⊢
  exact hxs.filter p

private theorem audit_nodup_map_of_injective
    {alpha beta : Type} (f : alpha → beta) (xs : List alpha)
    (hf : Function.Injective f) (hxs : xs.Nodup) :
    (xs.map f).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  apply (List.nodup_iff_pairwise_ne.mp hxs).imp
  intro a b hab heq
  exact hab (hf heq)

/-- A finite-list injection generated by an involution gives the corresponding
predicate-count inequality. -/
private theorem audit_countP_le_of_involution
    {alpha : Type} (xs : List alpha) (p q : alpha → Bool)
    (swap : alpha → alpha)
    (hnodup : xs.Nodup)
    (hinvol : ∀ x, swap (swap x) = x)
    (hmem : ∀ x, x ∈ xs → swap x ∈ xs)
    (hpq : ∀ x, x ∈ xs → p x = true → q (swap x) = true) :
    xs.countP p ≤ xs.countP q := by
  classical
  have hinj : Function.Injective swap := by
    intro x y hxy
    rw [← hinvol x, ← hinvol y, hxy]
  let selected := xs.filter p
  have hselectedNodup : selected.Nodup :=
    audit_nodup_filter_of_nodup p xs hnodup
  have himageNodup : (selected.map swap).Nodup :=
    audit_nodup_map_of_injective swap selected hinj hselectedNodup
  have hsubset : selected.map swap ⊆ xs.filter q := by
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [List.mem_filter] at hx ⊢
    exact ⟨hmem x hx.1, hpq x hx.1 hx.2⟩
  have hle := himageNodup.length_le_of_subset hsubset
  rw [List.length_map] at hle
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
  exact hle

/-- For every exact uniform scheduler layer, the two distinct persistent edge
labels win the first-relevant-clock race equally often.  This is an exact
finite-word count, not an iid or geometric-service premise. -/
theorem allSchedules_firstRelevant_front_rear_count_eq
    (front rear : Fin n) (hne : front ≠ rear) (t : Nat) :
    (allSchedules n t).countP
        (firstRelevantFrontWins front rear) =
      (allSchedules n t).countP
        (firstRelevantFrontWins rear front) := by
  classical
  let swap : DetSchedule n → DetSchedule n :=
    homeFrontReadySuffixSwap front rear
  have hinvol : ∀ word, swap (swap word) = word := by
    intro word
    exact homeFrontReadySuffixSwap_involutive front rear hne word
  have hmem : ∀ word, word ∈ allSchedules n t →
      swap word ∈ allSchedules n t := by
    intro word hword
    apply mem_allSchedules_of_length n t
    rw [homeFrontReadySuffixSwap_length]
    exact allSchedules_schedule_length n t word hword
  have hfrontToRear : ∀ word, word ∈ allSchedules n t →
      firstRelevantFrontWins front rear word = true →
      firstRelevantFrontWins rear front (swap word) = true := by
    intro word _hword hfront
    have hswap := firstRelevantFrontWins_swap front rear hne (swap word)
    change firstRelevantFrontWins front rear (swap (swap word)) =
      firstRelevantFrontWins rear front (swap word) at hswap
    rw [hinvol word] at hswap
    rw [← hswap]
    exact hfront
  have hrearToFront : ∀ word, word ∈ allSchedules n t →
      firstRelevantFrontWins rear front word = true →
      firstRelevantFrontWins front rear (swap word) = true := by
    intro word _hword hrear
    rw [firstRelevantFrontWins_swap front rear hne word]
    exact hrear
  apply Nat.le_antisymm
  · exact audit_countP_le_of_involution
      (allSchedules n t)
      (firstRelevantFrontWins front rear)
      (firstRelevantFrontWins rear front)
      swap (allSchedules_nodup n t) hinvol hmem hfrontToRear
  · exact audit_countP_le_of_involution
      (allSchedules n t)
      (firstRelevantFrontWins rear front)
      (firstRelevantFrontWins front rear)
      swap (allSchedules_nodup n t) hinvol hmem hrearToFront

/-- The same finite word cannot have both distinguished labels first. -/
theorem firstRelevantFrontWins_disjoint
    (front rear : Fin n) (hne : front ≠ rear)
    (word : DetSchedule n) :
    (firstRelevantFrontWins front rear word &&
      firstRelevantFrontWins rear front word) = false := by
  induction word with
  | nil => rfl
  | cons edge rest ih =>
      by_cases hef : edge = front
      · subst edge
        simp [firstRelevantFrontWins, hne, hne.symm]
      · by_cases her : edge = rear
        · subst edge
          simp [firstRelevantFrontWins, hne, hne.symm]
        · simp [firstRelevantFrontWins, hef, her, ih]

/-- Did either distinguished scheduler label occur? -/
def firstRelevantOccurs (front rear : Fin n)
    (word : DetSchedule n) : Bool :=
  firstRelevantFrontWins front rear word ||
    firstRelevantFrontWins rear front word

private theorem audit_countP_or_eq_add_of_disjoint
    {alpha : Type} (xs : List alpha) (p q : alpha → Bool)
    (hdisjoint : ∀ x, (p x && q x) = false) :
    xs.countP (fun x => p x || q x) =
      xs.countP p + xs.countP q := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx := hdisjoint x
      cases hp : p x <;> cases hq : q x <;>
        simp [hp, hq, ih] at hx ⊢ <;> omega

/-- Denominator-cleared conditional fairness: among exact length-`t` scheduler
words in which either persistent label appears, precisely half put `front`
first.  No limiting probability or freshness premise occurs in the statement. -/
theorem allSchedules_firstRelevant_occurs_count_eq_two_mul_front
    (front rear : Fin n) (hne : front ≠ rear) (t : Nat) :
    (allSchedules n t).countP (firstRelevantOccurs front rear) =
      2 * (allSchedules n t).countP
        (firstRelevantFrontWins front rear) := by
  rw [show (allSchedules n t).countP (firstRelevantOccurs front rear) =
      (allSchedules n t).countP
          (firstRelevantFrontWins front rear) +
        (allSchedules n t).countP
          (firstRelevantFrontWins rear front) by
    unfold firstRelevantOccurs
    apply audit_countP_or_eq_add_of_disjoint
    exact firstRelevantFrontWins_disjoint front rear hne]
  rw [allSchedules_firstRelevant_front_rear_count_eq front rear hne t]
  omega

/-! ## Why the domination must be embedded at front-hop epochs -/

/-- One event of the critical reflected queue: at zero a front arrival is
forced; at positive height the Boolean chooses front (`true`) or rear service
(`false`). -/
def reflectedTaggedEventStep (q : Nat) (frontWins : Bool) : Nat :=
  if q = 0 then 1 else if frontWins then q + 1 else q - 1

/-- The individual-event transition is not monotone in queue height.  Thus a
proof that merely shares event coins and inducts after every tagged event is
invalid: with the rear-service coin, `0 ≤ 1` is sent to `1 > 0`. -/
theorem reflectedTaggedEventStep_not_monotone :
    0 ≤ 1 /\
      reflectedTaggedEventStep 0 false >
        reflectedTaggedEventStep 1 false := by
  decide

/-- Queue height at the next front-hop epoch after `services` rear services.
Natural subtraction is the reflected maximum `max (q+1-services) 0`. -/
def frontEpochQueueStep (q services : Nat) : Nat :=
  q + 1 - services

/-- The exact pathwise arithmetic needed by the repaired Stage-II coupling.
Starting below the critical queue and inserting any number of extra rear
services preserves domination at the next front-hop epoch. -/
theorem frontEpochQueueStep_extra_service_le
    (q qhat sharedServices extraServices : Nat)
    (hq : q ≤ qhat) :
    frontEpochQueueStep q (sharedServices + extraServices) ≤
      frontEpochQueueStep qhat sharedServices := by
  unfold frontEpochQueueStep
  omega

/-- Exact finite-count statement whose proof is still the combinatorial
stopping-time obligation.  Naming it here prevents the local audit brick from
being misreported as a producer. -/
def HomeFrontCombinatorialSexticReadyOrABBound
    (ring : DirectedRing n)
    (X : Fin n -> SealSweepHomeFrontSite) : Prop :=
  n ^ (32 * n ^ 6) <=
    2 * homeFrontReadyOrABHitTree ring X (32 * n ^ 6)

#print axioms homeFrontXnor_differs_from_front_on_C_D
#print axioms homeFrontFront10At_localStep_of_ne_of_not_gate
#print axioms homeFront_homeBit_localStep_eq_of_not_gate
#print axioms corrected_DB_then_rearHop_exposes_ready
#print axioms corrected_targetA_changes_iff_rightC
#print axioms allSchedules_firstRelevant_front_rear_count_eq
#print axioms allSchedules_firstRelevant_occurs_count_eq_two_mul_front
#print axioms reflectedTaggedEventStep_not_monotone
#print axioms frontEpochQueueStep_extra_service_le

end PPartialSealSweepCombinatorialGateAuditSol
end PPLLCompleteMultiLeaderCleanup
