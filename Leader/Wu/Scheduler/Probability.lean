import Leader.Wu.Scheduler.WhpProfiles
import Leader.Wu.Scheduler.TraversalMetric

/-!
# Exact finite-scheduler semantics for convergence profiles

Unlike `ReachSpec`, this module defines an actual meaning for a finite-horizon
uniform random scheduler. Every length-`t` edge schedule is enumerated, and the
success probability is the exact rational fraction of schedules that visit the
postcondition at or before time `t`.

This elementary finite semantics avoids measure theory and is sufficient for
small-instance model checking and for stating honest certification obligations.
It is not yet scalable enough for the asymptotic Chernoff/Yokota proofs.
-/

/-- All edge schedules of exactly `t` interactions. Each extension appends one
of the `n` directed-ring edges. -/
def allSchedules (n : Nat) : Nat → List (DetSchedule n)
  | 0 => [[]]
  | t + 1 =>
      (allSchedules n t).flatMap (fun s =>
        List.ofFn (fun e : Fin n => s ++ [e]))

private theorem sum_map_const (xs : List α) (n : Nat) :
    (xs.map fun _ => n).sum = xs.length * n := by
  induction xs with
  | nil => simp
  | cons _ xs ih => simp [ih, Nat.add_mul, Nat.add_comm]

/-- There are exactly `n^t` length-`t` schedules. This proves that the
enumeration denominator is the intended uniform product-space cardinality. -/
theorem allSchedules_length (n t : Nat) :
    (allSchedules n t).length = n ^ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [allSchedules, List.length_flatMap, List.length_ofFn]
    rw [sum_map_const, ih, Nat.pow_succ]

/-- Every enumerated scheduler outcome has exactly the requested horizon. -/
theorem allSchedules_schedule_length (n t : Nat) :
    ∀ s ∈ allSchedules n t, s.length = t := by
  induction t with
  | zero =>
    intro s hs
    simp [allSchedules] at hs
    subst s
    rfl
  | succ t ih =>
    intro s hs
    simp only [allSchedules, List.mem_flatMap] at hs
    obtain ⟨pre, hpre, hs⟩ := hs
    simp only [List.mem_ofFn] at hs
    obtain ⟨e, heq⟩ := hs
    rw [← heq, List.length_append]
    simp only [List.length_cons, List.length_nil]
    rw [ih pre hpre]

/-- Conversely, every typed schedule of the requested length appears in the
enumeration. Together with `allSchedules_schedule_length`, this establishes
schedule-level completeness (the outcome-tree cardinality theorem tracks
multiplicity). -/
theorem mem_allSchedules_of_length (n t : Nat) (s : DetSchedule n)
    (hlen : s.length = t) : s ∈ allSchedules n t := by
  induction t generalizing s with
  | zero =>
    have hs : s = [] := List.eq_nil_of_length_eq_zero hlen
    subst s
    simp [allSchedules]
  | succ t ih =>
    have hne : s ≠ [] := by
      intro heq
      subst s
      simp at hlen
    let pre := s.dropLast
    let e := s.getLast hne
    have hprelen : pre.length = t := by
      simp only [pre, List.length_dropLast, hlen]
      omega
    have hpremem := ih pre hprelen
    simp only [allSchedules, List.mem_flatMap]
    refine ⟨pre, hpremem, ?_⟩
    rw [List.mem_ofFn]
    exact ⟨e, List.dropLast_concat_getLast hne⟩

/-- Whether a schedule visits `post` initially or after one of its steps. -/
def hitsWithin {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (post : (Fin n → AgentState ψ) → Bool) :
    (Fin n → AgentState ψ) → DetSchedule n → Bool
  | C, [] => post C
  | C, e :: rest =>
      post C || hitsWithin ring T post (stepConfig ring T C e) rest

/-- Reaching `post` at the end of a deterministic schedule implies that the
finite-horizon hitting test succeeds. -/
theorem hitsWithin_of_post_applySchedule
    {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (post : (Fin n → AgentState ψ) → Bool)
    (C : Fin n → AgentState ψ) (s : DetSchedule n)
    (hpost : post (applySchedule ring T C s) = true) :
    hitsWithin ring T post C s = true := by
  induction s generalizing C with
  | nil => exact hpost
  | cons e rest ih =>
    simp only [applySchedule] at hpost
    simp only [hitsWithin]
    have htail := ih (stepConfig ring T C e) hpost
    simp [htail]

/-- If a prefix has already hit `post`, extending the schedule cannot remove
that hit. -/
theorem hitsWithin_append_of_left
    {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (post : (Fin n → AgentState ψ) → Bool)
    (C : Fin n → AgentState ψ) (s padding : DetSchedule n)
    (h : hitsWithin ring T post C s = true) :
    hitsWithin ring T post C (s ++ padding) = true := by
  induction s generalizing C with
  | nil =>
    simp only [hitsWithin] at h
    cases padding <;> simp [hitsWithin, h]
  | cons e rest ih =>
    simp only [hitsWithin] at h
    simp only [List.cons_append, hitsWithin]
    cases hp : post C
    · have htail :
          hitsWithin ring T post (stepConfig ring T C e) rest = true := by
        simpa [hp] using h
      have hout := ih (stepConfig ring T C e) htail
      simpa [hp] using hout
    · simp

/-- Pad a schedule to horizon `t` with one fixed ring edge. -/
def padSchedule {n : Nat} (ring : DirectedRing n)
    (t : Nat) (s : DetSchedule n) : DetSchedule n :=
  s ++ List.replicate (t - s.length) ⟨0, ring.hn⟩

theorem padSchedule_length {n : Nat} (ring : DirectedRing n)
    (t : Nat) (s : DetSchedule n) (h : s.length ≤ t) :
    (padSchedule ring t s).length = t := by
  simp [padSchedule]
  omega

/-- Number of uniformly enumerated schedules that hit `post`. -/
def hitCount {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (post : (Fin n → AgentState ψ) → Bool)
    (C : Fin n → AgentState ψ) (t : Nat) : Nat :=
  (allSchedules n t).countP (hitsWithin ring T post C)

private theorem length_le_countP_of_sublist {α : Type}
    (p : α → Bool) {xs ys : List α} (hsub : xs.Sublist ys)
    (hgood : ∀ x, x ∈ xs → p x = true) :
    xs.length ≤ ys.countP p := by
  induction hsub with
  | slnil => simp
  | cons _ _ ih =>
    rw [List.countP_cons]
    have hi := ih hgood
    omega
  | @cons_cons l₁ _ a _ ih =>
    rw [List.length_cons, List.countP_cons]
    have ha : p a = true := hgood a (by simp)
    rw [if_pos ha]
    have htail : ∀ x, x ∈ l₁ → p x = true := by
      intro x hx
      exact hgood x (by simp [hx])
    have hi := ih htail
    omega

/-- Exact success probability under independent uniform edge choices. The
ring hypothesis ensures `n>0`, hence the schedule list is nonempty. -/
def hitProbability {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (post : (Fin n → AgentState ψ) → Bool)
    (C : Fin n → AgentState ψ) (t : Nat) : Rat :=
  (hitCount ring T post C t : Rat) / ((allSchedules n t).length : Nat)

/-- Exact finite deterministic-to-random counting bridge. Any favorable
sublist of the uniform schedule enumeration contributes its full cardinality to
the hit probability. `Sublist` tracks multiplicity, matching the scheduler
outcome tree without requiring `Finset` or Mathlib. -/
theorem hitProbability_lower_of_favorable_sublist
    {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (post : (Fin n → AgentState ψ) → Bool)
    (C : Fin n → AgentState ψ) (t : Nat)
    (favorable : List (DetSchedule n))
    (hsub : favorable.Sublist (allSchedules n t))
    (hgood : ∀ s, s ∈ favorable →
      hitsWithin ring T post C s = true) :
    (favorable.length : Rat) / ((allSchedules n t).length : Nat) ≤
      hitProbability ring T post C t := by
  have hc : favorable.length ≤ hitCount ring T post C t := by
    unfold hitCount
    exact length_le_countP_of_sublist _ hsub hgood
  unfold hitProbability
  have hdNat : 0 < (allSchedules n t).length := by
    rw [allSchedules_length]
    exact Nat.pow_pos ring.hn
  have hdRat : (0 : Rat) < ((allSchedules n t).length : Nat) := by
    rw [Rat.natCast_pos]
    exact hdNat
  apply Rat.le_of_mul_le_mul_right
    (c := ((allSchedules n t).length : Nat))
  · rw [Rat.div_mul_cancel (Rat.ne_of_lt hdRat).symm,
      Rat.div_mul_cancel (Rat.ne_of_lt hdRat).symm]
    rw [Rat.natCast_le_natCast]
    exact hc
  · exact hdRat

/-- Exact hit probabilities are nonnegative. -/
theorem hitProbability_nonneg
    {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (post : (Fin n → AgentState ψ) → Bool)
    (C : Fin n → AgentState ψ) (t : Nat) :
    (0 : Rat) ≤ hitProbability ring T post C t := by
  unfold hitProbability
  have hdNat : 0 < (allSchedules n t).length := by
    rw [allSchedules_length]
    exact Nat.pow_pos ring.hn
  have hdRat : (0 : Rat) < ((allSchedules n t).length : Nat) := by
    rw [Rat.natCast_pos]
    exact hdNat
  apply Rat.le_of_mul_le_mul_right
    (c := ((allSchedules n t).length : Nat))
  · rw [Rat.zero_mul,
      Rat.div_mul_cancel (Rat.ne_of_lt hdRat).symm]
    exact Rat.natCast_nonneg
  · exact hdRat

/-- Exact hit probabilities are at most one. -/
theorem hitProbability_le_one
    {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (post : (Fin n → AgentState ψ) → Bool)
    (C : Fin n → AgentState ψ) (t : Nat) :
    hitProbability ring T post C t ≤ 1 := by
  unfold hitProbability
  have hdNat : 0 < (allSchedules n t).length := by
    rw [allSchedules_length]
    exact Nat.pow_pos ring.hn
  have hdRat : (0 : Rat) < ((allSchedules n t).length : Nat) := by
    rw [Rat.natCast_pos]
    exact hdNat
  apply Rat.le_of_mul_le_mul_right
    (c := ((allSchedules n t).length : Nat))
  · rw [Rat.div_mul_cancel (Rat.ne_of_lt hdRat).symm, Rat.one_mul]
    rw [Rat.natCast_le_natCast]
    exact List.countP_le_length
  · exact hdRat

/-- A single deterministic favorable schedule of length `t` already gives an
exact lower bound `1/n^t` under the uniform scheduler. This is much weaker than
Yokota's polynomial-horizon lifting, but it is fully semantic and axiom-free. -/
theorem hitProbability_lower_of_one_schedule
    {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (post : (Fin n → AgentState ψ) → Bool)
    (C : Fin n → AgentState ψ) (t : Nat) (s : DetSchedule n)
    (hlen : s.length = t)
    (hgood : hitsWithin ring T post C s = true) :
    (1 : Rat) / (n ^ t : Nat) ≤ hitProbability ring T post C t := by
  have h := hitProbability_lower_of_favorable_sublist ring T post C t [s]
    (List.singleton_sublist.mpr (mem_allSchedules_of_length n t s hlen))
    (by
      intro x hx
      simp only [List.mem_singleton] at hx
      subst x
      exact hgood)
  simpa only [List.length_cons, List.length_nil, Nat.zero_add,
    allSchedules_length, Rat.natCast_ofNat] using h

/-- Reach profile induced by one favorable deterministic schedule from every
pre-state. Its success lower bound is the exact singleton probability `1/n^t`;
this is weak but semantic. -/
def oneScheduleProfile
    {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (Pre Post : (Fin n → AgentState ψ) → Prop) (t : Nat) :
    ReachSpec ring T where
  Pre := Pre
  Post := Post
  steps := fun _ => t
  failProb := fun n => (1 : Rat) - (1 : Rat) / (n ^ t : Nat)

/-- Honest finite-horizon validity of a profile. Besides deciding its `Post`,
a valid profile must satisfy the claimed probability bound for every initial
configuration satisfying `Pre`. -/
def ReachSpec.SemanticallyValid {ψ n : Nat} {ring : DirectedRing n}
    {T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ}
    (r : ReachSpec ring T)
    (postTest : (Fin n → AgentState ψ) → Bool) : Prop :=
  (∀ C, postTest C = true ↔ r.Post C) ∧
  ∀ C, r.Pre C →
    (1 : Rat) - r.failProb n ≤
      hitProbability ring T postTest C (r.steps n)

/-- A profile bundled with the semantic evidence that the old formalization
omitted. Future phase theorems should return this type (or a scalable semantic
equivalent), never a bare `ReachSpec`. -/
structure CertifiedReachSpec {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ) where
  spec : ReachSpec ring T
  postTest : (Fin n → AgentState ψ) → Bool
  valid : spec.SemanticallyValid postTest

/-- A deterministic favorable schedule for every pre-state semantically
certifies `oneScheduleProfile` under the exact uniform scheduler. -/
theorem oneScheduleProfile_semantically_valid
    {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (Pre Post : (Fin n → AgentState ψ) → Prop)
    (postTest : (Fin n → AgentState ψ) → Bool)
    (hdec : ∀ C, postTest C = true ↔ Post C)
    (t : Nat)
    (hdet : ∀ C, Pre C → ∃ s : DetSchedule n,
      s.length = t ∧ Post (applySchedule ring T C s)) :
    (oneScheduleProfile ring T Pre Post t).SemanticallyValid postTest := by
  refine ⟨hdec, ?_⟩
  intro C hpre
  obtain ⟨s, hlen, hpost⟩ := hdet C hpre
  have hhit : hitsWithin ring T postTest C s = true :=
    hitsWithin_of_post_applySchedule ring T postTest C s
      ((hdec _).2 hpost)
  have hlower := hitProbability_lower_of_one_schedule
    ring T postTest C t s hlen hhit
  have hcancel :
      (1 : Rat) - ((1 : Rat) - (1 : Rat) / (n ^ t : Nat)) =
        (1 : Rat) / (n ^ t : Nat) := by
    rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg, Rat.neg_add, Rat.neg_neg]
    rw [← Rat.add_assoc, Rat.add_neg_cancel, Rat.zero_add]
  rw [oneScheduleProfile, hcancel]
  exact hlower

/-- Variant whose deterministic premise directly provides a favorable hitting
schedule. -/
theorem oneScheduleProfile_semantically_valid_of_hit
    {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (Pre Post : (Fin n → AgentState ψ) → Prop)
    (postTest : (Fin n → AgentState ψ) → Bool)
    (hdec : ∀ C, postTest C = true ↔ Post C)
    (t : Nat)
    (hdet : ∀ C, Pre C → ∃ s : DetSchedule n,
      s.length = t ∧ hitsWithin ring T postTest C s = true) :
    (oneScheduleProfile ring T Pre Post t).SemanticallyValid postTest := by
  refine ⟨hdec, ?_⟩
  intro C hpre
  obtain ⟨s, hlen, hhit⟩ := hdet C hpre
  have hlower := hitProbability_lower_of_one_schedule
    ring T postTest C t s hlen hhit
  have hcancel :
      (1 : Rat) - ((1 : Rat) - (1 : Rat) / (n ^ t : Nat)) =
        (1 : Rat) / (n ^ t : Nat) := by
    rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg, Rat.neg_add, Rat.neg_neg]
    rw [← Rat.add_assoc, Rat.add_neg_cancel, Rat.zero_add]
  rw [oneScheduleProfile, hcancel]
  exact hlower

/-- A favorable deterministic schedule of length at most `t` also certifies
the profile: pad it to exactly `t`, retaining the earlier hit. -/
theorem oneScheduleProfile_semantically_valid_of_bounded_schedule
    {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (Pre Post : (Fin n → AgentState ψ) → Prop)
    (postTest : (Fin n → AgentState ψ) → Bool)
    (hdec : ∀ C, postTest C = true ↔ Post C)
    (t : Nat)
    (hdet : ∀ C, Pre C → ∃ s : DetSchedule n,
      s.length ≤ t ∧ Post (applySchedule ring T C s)) :
    (oneScheduleProfile ring T Pre Post t).SemanticallyValid postTest := by
  apply oneScheduleProfile_semantically_valid_of_hit
    ring T Pre Post postTest hdec t
  intro C hpre
  obtain ⟨s, hlen, hpost⟩ := hdet C hpre
  let padded := padSchedule ring t s
  refine ⟨padded, padSchedule_length ring t s hlen, ?_⟩
  apply hitsWithin_append_of_left ring T postTest C s
    (List.replicate (t - s.length) ⟨0, ring.hn⟩)
  exact hitsWithin_of_post_applySchedule ring T postTest C s
    ((hdec _).2 hpost)

/-- Certified constructor for the one-favorable-schedule lift. -/
def CertifiedReachSpec.of_one_schedule
    {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (Pre Post : (Fin n → AgentState ψ) → Prop)
    (postTest : (Fin n → AgentState ψ) → Bool)
    (hdec : ∀ C, postTest C = true ↔ Post C)
    (t : Nat)
    (hdet : ∀ C, Pre C → ∃ s : DetSchedule n,
      s.length = t ∧ Post (applySchedule ring T C s)) :
    CertifiedReachSpec ring T where
  spec := oneScheduleProfile ring T Pre Post t
  postTest := postTest
  valid := oneScheduleProfile_semantically_valid
    ring T Pre Post postTest hdec t hdet

/-- Certified bounded-schedule constructor. -/
def CertifiedReachSpec.of_bounded_schedule
    {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (Pre Post : (Fin n → AgentState ψ) → Prop)
    (postTest : (Fin n → AgentState ψ) → Bool)
    (hdec : ∀ C, postTest C = true ↔ Post C)
    (t : Nat)
    (hdet : ∀ C, Pre C → ∃ s : DetSchedule n,
      s.length ≤ t ∧ Post (applySchedule ring T C s)) :
    CertifiedReachSpec ring T where
  spec := oneScheduleProfile ring T Pre Post t
  postTest := postTest
  valid := oneScheduleProfile_semantically_valid_of_bounded_schedule
    ring T Pre Post postTest hdec t hdet

/-- Honest deterministic-traversal lift. It certifies only the singleton
schedule bound `1/n^(k*n)`, not the metadata-only Yokota/Chernoff bound. -/
def CertifiedReachSpec.of_traversal_family
    {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    {α : Type}
    (M : TraversalMetric ψ n ring T α)
    (Pre Post : (Fin n → AgentState ψ) → Prop)
    (postTest : (Fin n → AgentState ψ) → Bool)
    (hdec : ∀ C, postTest C = true ↔ Post C)
    (objects : (Fin n → AgentState ψ) → List α)
    (k : Nat)
    (hk : ∀ C, Pre C → (objects C).length ≤ k)
    (hgoal : ∀ C s, Pre C →
      (∀ obj, obj ∈ objects C → M.goal (applySchedule ring T C s) obj) →
      Post (applySchedule ring T C s)) :
    CertifiedReachSpec ring T :=
  CertifiedReachSpec.of_bounded_schedule ring T Pre Post postTest hdec
    (k * n) (by
      intro C hpre
      obtain ⟨s, hslen, hsgoal⟩ := traversal_bound_family M (objects C) C
      refine ⟨s, ?_, hgoal C s hpre hsgoal⟩
      exact Nat.le_trans hslen (Nat.mul_le_mul_right n (hk C hpre)))

/-- The zero-step identity profile has a genuine semantic proof whenever its
Boolean post-test decides the predicate. -/
theorem ReachSpec.identity_semantically_valid
    {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (P : (Fin n → AgentState ψ) → Prop)
    (postTest : (Fin n → AgentState ψ) → Bool)
    (hdec : ∀ C, postTest C = true ↔ P C) :
    (ReachSpec.identity ring T P).SemanticallyValid postTest := by
  refine ⟨hdec, ?_⟩
  intro C hP
  have ht : postTest C = true := (hdec C).2 hP
  simp only [ReachSpec.identity, StepBound.zero, FailBound.zero,
    hitProbability, hitCount, allSchedules, List.countP_cons, List.countP_nil,
    hitsWithin, ht, if_pos, Nat.zero_add, List.length_cons, List.length_nil]
  rw [Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero]
  have hzeroone : (0 : Rat) < 1 := by rw [Rat.lt_iff]; decide
  have hone : (1 : Rat) ≠ 0 := (Rat.ne_of_lt hzeroone).symm
  have hdiv := Rat.div_mul_cancel (a := (1 : Rat)) (b := 1) hone
  rw [Rat.mul_one] at hdiv
  simp only [Rat.natCast_ofNat]
  rw [hdiv]
  exact Rat.le_refl

/-- First genuinely certified profile constructor. -/
def CertifiedReachSpec.identity
    {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (P : (Fin n → AgentState ψ) → Prop)
    (postTest : (Fin n → AgentState ψ) → Bool)
    (hdec : ∀ C, postTest C = true ↔ P C) : CertifiedReachSpec ring T where
  spec := ReachSpec.identity ring T P
  postTest := postTest
  valid := ReachSpec.identity_semantically_valid ring T P postTest hdec

/-- A metadata profile can claim an impossible zero-failure result. The new
semantics rejects it, illustrating exactly what `ReachSpec` alone omitted. -/
def falseProfile {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ) :
    ReachSpec ring T where
  Pre := fun _ => True
  Post := fun _ => False
  steps := StepBound.zero
  failProb := FailBound.zero

theorem falseProfile_not_semantically_valid
    {ψ n : Nat} (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (C : Fin n → AgentState ψ) :
    ¬(falseProfile ring T).SemanticallyValid (fun _ => false) := by
  intro h
  have hbound := h.2 C trivial
  simp [falseProfile, StepBound.zero, FailBound.zero, hitProbability,
    hitCount, allSchedules, hitsWithin] at hbound
  rw [Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero,
    Rat.div_def, Rat.zero_mul] at hbound
  have hn : ¬((1 : Rat) ≤ 0) := by
    rw [Rat.not_le, Rat.lt_iff]
    decide
  exact hn hbound

