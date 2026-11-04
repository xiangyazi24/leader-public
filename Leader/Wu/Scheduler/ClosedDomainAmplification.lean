import Leader.Wu.Scheduler.RepeatedBlocks

/-!
# Exact random-scheduler amplification on a closed configuration domain

`SchedulerBlocks` multiplies a block miss budget when that budget is uniform
over every configuration.  Protocol repair arguments usually have a narrower
shape: a producer is valid only on an authorized configuration domain.  To
reuse it after an arbitrary random prefix, that domain must be closed under
every local step.

This file proves the missing closed-domain composition.  If every nonsafe
configuration in a step-closed domain has some schedule of length at most
`L` reaching a decidable target, then one iid uniform-edge block has at most
`n^L - 1` misses.  After `k` aligned blocks the exact miss count is at most
`(n^L - 1)^k` among the `n^(k*L)` scheduler outcomes.  No probabilistic
independence axiom is used: the multiplication is the existing exact list
product decomposition of uniform schedules.

Finiteness of the local carrier is not needed by the amplification theorem
once the uniform bound `L` is supplied.  A finite carrier/domain is one way to
construct such a uniform bound from pointwise reachability, but that separate
maximum-producing argument is not assumed here.
-/

namespace PPLLClosedDomainSchedulerAmplificationSol

open PPLLResearchFormulation
open PPLLTraceConvergence
open PPLLSchedulerBlocks

set_option autoImplicit false

/-! ## Closed domains and bounded target producers -/

/-- A configuration predicate preserved by every exact local interaction. -/
def LocalStepClosed {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (Domain : (Fin n → Q) → Prop) : Prop :=
  ∀ C, Domain C → ∀ e, Domain (localStep ring T C e)

/-- Every nonsafe state in `Domain` has a concrete schedule of length at most
`L` whose endpoint satisfies `Safe`.  The producer is required again at every
nonsafe suffix state; it is not merely a producer for the original start. -/
def BoundedSafeScheduleProducer {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (Domain Safe : (Fin n → Q) → Prop) (L : Nat) : Prop :=
  ∀ C, Domain C → ¬ Safe C →
    ∃ word : DetSchedule n,
      word.length ≤ L ∧ Safe (runLocalSchedule ring T C word)

/-- Step closure propagates through every finite exact schedule. -/
theorem localStepClosed_runLocalSchedule
    {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (Domain : (Fin n → Q) → Prop)
    (hclosed : LocalStepClosed ring T Domain)
    {C : Fin n → Q} (hC : Domain C) (word : DetSchedule n) :
    Domain (runLocalSchedule ring T C word) := by
  induction word generalizing C with
  | nil => exact hC
  | cons e rest ih =>
      simp only [runLocalSchedule]
      exact ih (hclosed C hC e)

/-! ## Endpoint and initial-state hitting lemmas -/

/-- If the endpoint of a word satisfies the Boolean target, the prefix-hitting
test succeeds. -/
theorem hitsWithinLocal_of_endpoint
    {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (postTest : (Fin n → Q) → Bool)
    (C : Fin n → Q) (word : DetSchedule n)
    (hpost : postTest (runLocalSchedule ring T C word) = true) :
    hitsWithinLocal ring T postTest C word = true := by
  induction word generalizing C with
  | nil => exact hpost
  | cons e rest ih =>
      simp only [runLocalSchedule] at hpost
      simp only [hitsWithinLocal]
      have htail := ih (localStep ring T C e) hpost
      simp [htail]

/-- A target already true at the block start is hit by every schedule. -/
theorem hitsWithinLocal_of_initial
    {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (postTest : (Fin n → Q) → Bool)
    (C : Fin n → Q) (word : DetSchedule n)
    (hpost : postTest C = true) :
    hitsWithinLocal ring T postTest C word = true := by
  cases word <;> simp [hitsWithinLocal, hpost]

/-- If `Safe` is step-closed, every schedule that hits it also ends in it.
Closedness is needed for this endpoint interpretation, but not for the miss
count itself. -/
theorem hitsWithinLocal_closed_endpoint
    {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (Safe : (Fin n → Q) → Prop)
    (safeTest : (Fin n → Q) → Bool)
    (hdec : ∀ C, safeTest C = true ↔ Safe C)
    (hclosed : LocalStepClosed ring T Safe)
    (C : Fin n → Q) (word : DetSchedule n)
    (hhit : hitsWithinLocal ring T safeTest C word = true) :
    Safe (runLocalSchedule ring T C word) := by
  induction word generalizing C with
  | nil =>
      exact (hdec C).1 hhit
  | cons e rest ih =>
      simp only [hitsWithinLocal] at hhit
      cases hstart : safeTest C with
      | false =>
          have htail :
              hitsWithinLocal ring T safeTest
                (localStep ring T C e) rest = true := by
            simpa [hstart] using hhit
          exact ih (localStep ring T C e) htail
      | true =>
          have hsafe : Safe C := (hdec C).1 hstart
          exact localStepClosed_runLocalSchedule
            ring T Safe hclosed (hclosed C hsafe e) rest

/-- For a step-closed decidable target, prefix hitting and endpoint membership
are equivalent.  Thus the miss counts below can also be read literally as
endpoint-failure counts when the target is closed. -/
theorem hitsWithinLocal_iff_closed_endpoint
    {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (Safe : (Fin n → Q) → Prop)
    (safeTest : (Fin n → Q) → Bool)
    (hdec : ∀ C, safeTest C = true ↔ Safe C)
    (hclosed : LocalStepClosed ring T Safe)
    (C : Fin n → Q) (word : DetSchedule n) :
    hitsWithinLocal ring T safeTest C word = true ↔
      Safe (runLocalSchedule ring T C word) := by
  constructor
  · exact hitsWithinLocal_closed_endpoint
      ring T Safe safeTest hdec hclosed C word
  · intro hend
    exact hitsWithinLocal_of_endpoint ring T safeTest C word
      ((hdec _).2 hend)

/-! ## One exact block from the bounded producer -/

/-- The bounded producer yields an exact length-`L` favorable outcome.  If the
state is already safe, every word is favorable.  Otherwise the producer word
is padded after its first hit. -/
theorem boundedSafeProducer_exact_hit_schedule
    {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (Domain Safe : (Fin n → Q) → Prop)
    (safeTest : (Fin n → Q) → Bool)
    (hdec : ∀ C, safeTest C = true ↔ Safe C)
    (L : Nat)
    (hproducer : BoundedSafeScheduleProducer ring T Domain Safe L)
    (C : Fin n → Q) (hC : Domain C) :
    ∃ word : DetSchedule n,
      word.length = L ∧
        hitsWithinLocal ring T safeTest C word = true := by
  by_cases hsafe : Safe C
  · let word : DetSchedule n :=
      List.replicate L (⟨0, ring.hn⟩ : Fin n)
    refine ⟨word, by simp [word], ?_⟩
    exact hitsWithinLocal_of_initial ring T safeTest C word
      ((hdec C).2 hsafe)
  · obtain ⟨pre, hlength, hend⟩ := hproducer C hC hsafe
    let padding : DetSchedule n :=
      List.replicate (L - pre.length) (⟨0, ring.hn⟩ : Fin n)
    let word := pre ++ padding
    refine ⟨word, ?_, ?_⟩
    · simp [word, padding]
      omega
    · have hprefix :
          hitsWithinLocal ring T safeTest C pre = true :=
        hitsWithinLocal_of_endpoint ring T safeTest C pre
          ((hdec _).2 hend)
      dsimp [word]
      rw [hitsWithinLocal_append, hprefix]
      rfl

/-- Every domain state has at least one favorable length-`L` scheduler
outcome. -/
theorem localHitCount_pos_of_boundedSafeProducer
    {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (Domain Safe : (Fin n → Q) → Prop)
    (safeTest : (Fin n → Q) → Bool)
    (hdec : ∀ C, safeTest C = true ↔ Safe C)
    (L : Nat)
    (hproducer : BoundedSafeScheduleProducer ring T Domain Safe L)
    (C : Fin n → Q) (hC : Domain C) :
    0 < localHitCount ring T safeTest C L := by
  obtain ⟨word, hlength, hhit⟩ :=
    boundedSafeProducer_exact_hit_schedule
      ring T Domain Safe safeTest hdec L hproducer C hC
  unfold localHitCount
  apply List.countP_pos_iff.mpr
  exact ⟨word, mem_allSchedules_of_length n L word hlength, hhit⟩

/-- A single iid uniform-edge block has at most `n^L - 1` misses from every
state in the domain. -/
theorem boundedSafeProducer_oneBlockPhase
    {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (Domain Safe : (Fin n → Q) → Prop)
    (safeTest : (Fin n → Q) → Bool)
    (hdec : ∀ C, safeTest C = true ↔ Safe C)
    (L : Nat)
    (hproducer : BoundedSafeScheduleProducer ring T Domain Safe L) :
    UniformFinitePhase ring T Domain Safe safeTest
      L (n ^ L - 1) := by
  constructor
  · exact hdec
  · intro C hC
    rw [allSchedules_length]
    have hhit : 0 < localHitCount ring T safeTest C L :=
      localHitCount_pos_of_boundedSafeProducer
        ring T Domain Safe safeTest hdec L hproducer C hC
    have htotal : 0 < n ^ L := Nat.pow_pos ring.hn
    omega

/-! ## Closed-domain block multiplication -/

private theorem sum_if_false_le_countP_not_mul_on_domain
    {α : Type} (p : α → Bool) (f : α → Nat)
    (xs : List α) (B : Nat)
    (hf : ∀ x, x ∈ xs → p x = false → f x ≤ B) :
    (xs.map (fun x => if p x then 0 else f x)).sum ≤
      xs.countP (fun x => !p x) * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have htail : ∀ y, y ∈ xs → p y = false → f y ≤ B := by
        intro y hy
        exact hf y (by simp [hy])
      have hi := ih htail
      rw [List.map_cons, List.sum_cons, List.countP_cons]
      cases hp : p x
      · have hx : f x ≤ B := hf x (by simp) hp
        simpa [hp, Nat.add_mul, Nat.add_comm] using Nat.add_le_add hx hi
      · simpa [hp] using hi

/-- Closed-domain version of `localMissCount_add_le_mul`.  Domain closure is
the exact premise that makes the suffix-state budget available after every
random prefix. -/
theorem localMissCount_add_le_mul_on_closedDomain
    {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (Domain : (Fin n → Q) → Prop)
    (postTest : (Fin n → Q) → Bool)
    (hclosed : LocalStepClosed ring T Domain)
    (a b A B : Nat)
    (hA : ∀ C : Fin n → Q,
      Domain C → localMissCount ring T postTest C a ≤ A)
    (hB : ∀ C : Fin n → Q,
      Domain C → localMissCount ring T postTest C b ≤ B) :
    ∀ C : Fin n → Q, Domain C →
      localMissCount ring T postTest C (a + b) ≤ A * B := by
  intro C hC
  rw [localMissCount_add_eq_sum]
  let p := hitsWithinLocal ring T postTest C
  let f := fun pre => localMissCount ring T postTest
    (runLocalSchedule ring T C pre) b
  have hsum :
      ((allSchedules n a).map
        (fun pre => if p pre then 0 else f pre)).sum ≤
        (allSchedules n a).countP (fun pre => !p pre) * B := by
    apply sum_if_false_le_countP_not_mul_on_domain
    intro pre hpre hp
    exact hB _ (localStepClosed_runLocalSchedule
      ring T Domain hclosed hC pre)
  have hprefix :
      (allSchedules n a).countP (fun pre => !p pre) ≤ A := by
    exact hA C hC
  exact Nat.le_trans hsum (Nat.mul_le_mul_right B hprefix)

/-- Repeating a block inside a closed domain gives the exact geometric miss
budget `F^k`. -/
theorem localMissCount_repeatedBlock_le_on_closedDomain
    {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (Domain : (Fin n → Q) → Prop)
    (postTest : (Fin n → Q) → Bool)
    (hclosed : LocalStepClosed ring T Domain)
    (t F : Nat)
    (hF : ∀ C : Fin n → Q,
      Domain C → localMissCount ring T postTest C t ≤ F) :
    ∀ k C, Domain C →
      localMissCount ring T postTest C (k * t) ≤ F ^ k := by
  intro k
  induction k with
  | zero =>
      intro C hC
      have hlen : localMissCount ring T postTest C 0 ≤
          (allSchedules n 0).length := by
        unfold localMissCount
        exact List.countP_le_length
      simpa [allSchedules] using hlen
  | succ k ih =>
      intro C hC
      have hmul := localMissCount_add_le_mul_on_closedDomain
        ring T Domain postTest hclosed
        (k * t) t (F ^ k) F ih hF C hC
      simpa [Nat.succ_mul, Nat.pow_succ] using hmul

/-- A finite-phase certificate on a closed domain amplifies across aligned
blocks without strengthening its precondition to all configurations. -/
theorem uniformFinitePhase_repeatedBlock_on_closedDomain
    {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (Domain Post : (Fin n → Q) → Prop)
    (postTest : (Fin n → Q) → Bool)
    (hclosed : LocalStepClosed ring T Domain)
    (t F : Nat)
    (hphase : UniformFinitePhase ring T Domain Post postTest t F) :
    ∀ k, UniformFinitePhase ring T Domain Post postTest
      (k * t) (F ^ k) := by
  have hone : ∀ C : Fin n → Q,
      Domain C → localMissCount ring T postTest C t ≤ F := by
    intro C hC
    have hbudget := hphase.2 C hC
    have hpartition := localMissCount_add_localHitCount
      ring T postTest C t
    omega
  intro k
  constructor
  · exact hphase.1
  · intro C hC
    have hmiss := localMissCount_repeatedBlock_le_on_closedDomain
      ring T Domain postTest hclosed t F hone k C hC
    have hpartition := localMissCount_add_localHitCount
      ring T postTest C (k * t)
    omega

/-- Increasing an explicit failure budget preserves a finite-phase
certificate. -/
theorem uniformFinitePhase_mono_failures
    {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (Pre Post : (Fin n → Q) → Prop)
    (postTest : (Fin n → Q) → Bool)
    (t F G : Nat)
    (hphase : UniformFinitePhase ring T Pre Post postTest t F)
    (hFG : F ≤ G) :
    UniformFinitePhase ring T Pre Post postTest t G := by
  constructor
  · exact hphase.1
  · intro C hC
    exact Nat.le_trans (hphase.2 C hC)
      (Nat.add_le_add_left hFG _)

/-! ## Exact finite-horizon amplification -/

/-- Main count theorem.  At horizon `k*L`, at most `(n^L-1)^k` of the
`n^(k*L)` iid uniform-edge outcomes miss `Safe`. -/
theorem boundedSafeProducer_repeatedBlockPhase
    {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (Domain Safe : (Fin n → Q) → Prop)
    (safeTest : (Fin n → Q) → Bool)
    (hdec : ∀ C, safeTest C = true ↔ Safe C)
    (hDomainClosed : LocalStepClosed ring T Domain)
    (L : Nat)
    (hproducer : BoundedSafeScheduleProducer ring T Domain Safe L) :
    ∀ k, UniformFinitePhase ring T Domain Safe safeTest
      (k * L) ((n ^ L - 1) ^ k) := by
  exact uniformFinitePhase_repeatedBlock_on_closedDomain
    ring T Domain Safe safeTest hDomainClosed
    L (n ^ L - 1)
    (boundedSafeProducer_oneBlockPhase
      ring T Domain Safe safeTest hdec L hproducer)

/-- Any requested finite failure budget above the geometric miss count is
certified at the same horizon. -/
theorem boundedSafeProducer_finiteHorizonPhase
    {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (Domain Safe : (Fin n → Q) → Prop)
    (safeTest : (Fin n → Q) → Bool)
    (hdec : ∀ C, safeTest C = true ↔ Safe C)
    (hDomainClosed : LocalStepClosed ring T Domain)
    (L k allowedFailures : Nat)
    (hproducer : BoundedSafeScheduleProducer ring T Domain Safe L)
    (hbudget : (n ^ L - 1) ^ k ≤ allowedFailures) :
    UniformFinitePhase ring T Domain Safe safeTest
      (k * L) allowedFailures := by
  exact uniformFinitePhase_mono_failures
    ring T Domain Safe safeTest
    (k * L) ((n ^ L - 1) ^ k) allowedFailures
    (boundedSafeProducer_repeatedBlockPhase
      ring T Domain Safe safeTest hdec hDomainClosed L hproducer k)
    hbudget

/-- Exact finite `c/n`-shaped amplification.  The first conjunct proves that
the chosen failure budget is strictly smaller than the full outcome space, so
the statement is not satisfied by budgeting every schedule. -/
theorem boundedSafeProducer_oneOverNPhase
    {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (Domain Safe : (Fin n → Q) → Prop)
    (safeTest : (Fin n → Q) → Bool)
    (hdec : ∀ C, safeTest C = true ↔ Safe C)
    (hDomainClosed : LocalStepClosed ring T Domain)
    (L k c : Nat)
    (hproducer : BoundedSafeScheduleProducer ring T Domain Safe L)
    (hc : c < n) (horizonPos : 0 < k * L)
    (hbudget : (n ^ L - 1) ^ k ≤ c * n ^ (k * L - 1)) :
    c * n ^ (k * L - 1) < (allSchedules n (k * L)).length ∧
      UniformFinitePhase ring T Domain Safe safeTest
        (k * L) (c * n ^ (k * L - 1)) := by
  constructor
  · exact oneOverNFailure_budget_lt_total ring c (k * L) hc horizonPos
  · exact boundedSafeProducer_finiteHorizonPhase
      ring T Domain Safe safeTest hdec hDomainClosed
      L k (c * n ^ (k * L - 1)) hproducer hbudget

/-! ## An explicit finite `1/n` horizon -/

/-- The first two terms of the binomial expansion, proved without invoking a
probability limit theorem. -/
private theorem firstOrderBinomialLower (a m : Nat) :
    a ^ (m + 1) + (m + 1) * a ^ m ≤ (a + 1) ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hmul := Nat.mul_le_mul_right (a + 1) ih
      have hfirst :
          a ^ (Nat.succ m + 1) +
              (Nat.succ m + 1) * a ^ Nat.succ m ≤
            (a ^ (m + 1) + (m + 1) * a ^ m) * (a + 1) := by
        calc
          a ^ (Nat.succ m + 1) +
                (Nat.succ m + 1) * a ^ Nat.succ m ≤
              a ^ (Nat.succ m + 1) +
                  (Nat.succ m + 1) * a ^ Nat.succ m +
                    (m + 1) * a ^ m :=
            Nat.le_add_right _ _
          _ = (a ^ (m + 1) + (m + 1) * a ^ m) *
                (a + 1) := by
            simp only [Nat.succ_eq_add_one, Nat.pow_succ,
              Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one,
              Nat.mul_assoc]
            ac_rfl
      simpa only [Nat.succ_eq_add_one] using Nat.le_trans hfirst (by
        simpa only [Nat.pow_succ] using hmul)

/-- A completely explicit block count turns the geometric miss budget into a
finite `1/n` bound.  The horizon is intentionally crude:
`k = (n-1)(n^L-1)+1` blocks. -/
theorem geometricMiss_oneOverN_budget
    {n : Nat} (ring : DirectedRing n)
    (hn2 : 1 < n) (L : Nat) (hL : 0 < L) :
    let k := (n - 1) * (n ^ L - 1) + 1
    (n ^ L - 1) ^ k ≤ n ^ (k * L - 1) := by
  dsimp only
  let N := n ^ L
  let a := N - 1
  let m := (n - 1) * a
  let k := m + 1
  have hn1 : 1 ≤ n := by omega
  have hNpos : 0 < N := by
    exact Nat.pow_pos ring.hn
  have hNdecomp : a + 1 = N := by
    exact Nat.sub_add_cancel (by omega)
  have hmBound : (n - 1) * a ≤ m + 1 := by
    simp [m]
  have hmulBound :
      ((n - 1) * a) * a ^ m ≤ (m + 1) * a ^ m :=
    Nat.mul_le_mul_right (a ^ m) hmBound
  have hnDecomp : n = (n - 1) + 1 := by omega
  have hfront :
      n * a ^ (m + 1) ≤
        a ^ (m + 1) + (m + 1) * a ^ m := by
    calc
      n * a ^ (m + 1) =
          ((n - 1) + 1) * a ^ (m + 1) :=
        congrArg (fun x => x * a ^ (m + 1)) hnDecomp
      _ =
          a ^ (m + 1) + ((n - 1) * a) * a ^ m := by
        simp only [Nat.pow_succ, Nat.add_mul, Nat.one_mul,
          Nat.mul_assoc]
        ac_rfl
      _ ≤ a ^ (m + 1) + (m + 1) * a ^ m :=
        Nat.add_le_add_left hmulBound _
  have hscaled : n * a ^ k ≤ N ^ k := by
    change n * a ^ (m + 1) ≤ N ^ (m + 1)
    exact Nat.le_trans hfront (by
      simpa only [hNdecomp] using firstOrderBinomialLower a m)
  have hk : 0 < k := by simp [k]
  have hhorizon : 0 < k * L := Nat.mul_pos hk hL
  have htotal : N ^ k = n ^ (k * L) := by
    simp [N, Nat.pow_mul, Nat.mul_comm]
  have hfactor : n ^ (k * L) = n * n ^ (k * L - 1) := by
    obtain ⟨u, hu⟩ := Nat.exists_eq_succ_of_ne_zero
      (by omega : k * L ≠ 0)
    simp [hu, Nat.pow_succ, Nat.mul_comm]
  have hcancel : n * a ^ k ≤ n * n ^ (k * L - 1) := by
    calc
      n * a ^ k ≤ N ^ k := hscaled
      _ = n ^ (k * L) := htotal
      _ = n * n ^ (k * L - 1) := hfactor
  have hbudget : a ^ k ≤ n ^ (k * L - 1) :=
    Nat.le_of_mul_le_mul_left hcancel ring.hn
  change a ^ k ≤ n ^ (k * L - 1)
  exact hbudget

/-- The bounded producer therefore has an explicit positive horizon with at
most `1/n` failures, with no residual arithmetic premise. -/
theorem boundedSafeProducer_explicitOneOverNPhase
    {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (Domain Safe : (Fin n → Q) → Prop)
    (safeTest : (Fin n → Q) → Bool)
    (hdec : ∀ C, safeTest C = true ↔ Safe C)
    (hDomainClosed : LocalStepClosed ring T Domain)
    (hn2 : 1 < n) (L : Nat) (hL : 0 < L)
    (hproducer : BoundedSafeScheduleProducer ring T Domain Safe L) :
    let k := (n - 1) * (n ^ L - 1) + 1
    1 * n ^ (k * L - 1) < (allSchedules n (k * L)).length ∧
      UniformFinitePhase ring T Domain Safe safeTest
        (k * L) (1 * n ^ (k * L - 1)) := by
  let k := (n - 1) * (n ^ L - 1) + 1
  have hk : 0 < k := by simp [k]
  exact boundedSafeProducer_oneOverNPhase
    ring T Domain Safe safeTest hdec hDomainClosed
    L k 1 hproducer hn2 (Nat.mul_pos hk hL)
    (by simpa using geometricMiss_oneOverN_budget ring hn2 L hL)

/-! ## Bridge to genuine Definition-1 safety counts -/

/-- Domain-restricted counterpart of `UniformFiniteHorizonSSLE`. -/
def UniformFiniteHorizonSSLEOn
    (P : PopulationProtocol) {n : Nat}
    (ring : DirectedRing n) (isLeader : P.Y → Bool)
    (Domain : P.Configuration n → Prop)
    (t allowedFailures : Nat) : Prop :=
  ∀ C : P.Configuration n, Domain C →
    (allSchedules n t).length ≤
      stabilizingScheduleCount P ring isLeader C t + allowedFailures

/-- Domain-restricted finite `c/n` failure statement for genuine Definition-1
safety. -/
def UniformOneOverNFailureAtHorizonOn
    (P : PopulationProtocol) {n : Nat}
    (ring : DirectedRing n) (isLeader : P.Y → Bool)
    (Domain : P.Configuration n → Prop)
    (c t : Nat) : Prop :=
  c < n ∧ 0 < t ∧
    UniformFiniteHorizonSSLEOn P ring isLeader Domain
      t (c * n ^ (t - 1))

private theorem hitsWithinLocal_implies_post_prefix
    {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (Post : (Fin n → Q) → Prop)
    (postTest : (Fin n → Q) → Bool)
    (hdec : ∀ C, postTest C = true ↔ Post C)
    (C : Fin n → Q) (word : DetSchedule n)
    (hhit : hitsWithinLocal ring T postTest C word = true) :
    ∃ k : Nat, k ≤ word.length ∧
      Post (runLocalSchedule ring T C (word.take k)) := by
  induction word generalizing C with
  | nil =>
      refine ⟨0, by simp, ?_⟩
      exact (hdec C).1 hhit
  | cons e rest ih =>
      simp only [hitsWithinLocal] at hhit
      cases hstart : postTest C with
      | false =>
          have htail : hitsWithinLocal ring T postTest
              (localStep ring T C e) rest = true := by
            simpa [hstart] using hhit
          obtain ⟨k, hk, hpost⟩ :=
            ih (localStep ring T C e) htail
          refine ⟨k + 1, by simp; omega, ?_⟩
          simpa [runLocalSchedule] using hpost
      | true =>
          refine ⟨0, by simp, ?_⟩
          exact (hdec C).1 hstart

private theorem countP_le_countP_of_true_imp
    {α : Type} (p q : α → Bool) (xs : List α)
    (himp : ∀ x, x ∈ xs → p x = true → q x = true) :
    xs.countP p ≤ xs.countP q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have htail : ∀ y, y ∈ xs → p y = true → q y = true := by
        intro y hy
        exact himp y (by simp [hy])
      have hi := ih htail
      rw [List.countP_cons, List.countP_cons]
      cases hp : p x with
      | false =>
          cases q x <;> simp_all <;> omega
      | true =>
          have hq : q x = true := himp x (by simp) hp
          simpa [hp, hq] using hi

/-- Every schedule counted by the Boolean local hitting semantics is counted
by the repository's genuine semantic-safety scheduler count. -/
theorem localHitCount_le_stabilizingScheduleCount
    (P : PopulationProtocol) {n : Nat}
    (ring : DirectedRing n) (isLeader : P.Y → Bool)
    (safeTest : P.Configuration n → Bool)
    (hdec : ∀ C, safeTest C = true ↔
      PopulationProtocol.IsSafe P ring C isLeader)
    (C : P.Configuration n) (t : Nat) :
    localHitCount ring P.transition safeTest C t ≤
      stabilizingScheduleCount P ring isLeader C t := by
  classical
  unfold localHitCount stabilizingScheduleCount
  apply countP_le_countP_of_true_imp
  intro word hword hhit
  obtain ⟨k, hk, hsafe⟩ := hitsWithinLocal_implies_post_prefix
    ring P.transition
    (fun D => PopulationProtocol.IsSafe P ring D isLeader)
    safeTest hdec C word hhit
  have hrun := runLocalSchedule_eq_runSchedule
    P ring C (word.take k)
  rw [hrun] at hsafe
  have hreaches : ReachesSafeWithinSchedule
      P ring isLeader C word := ⟨k, hk, hsafe⟩
  simp [hreaches]

/-- A local finite-phase certificate whose target is Definition-1 safety gives
the exact domain-restricted SSLE schedule-count bound. -/
theorem uniformFinitePhase_isSafe_to_SSLEOn
    (P : PopulationProtocol) {n : Nat}
    (ring : DirectedRing n) (isLeader : P.Y → Bool)
    (Domain : P.Configuration n → Prop)
    (safeTest : P.Configuration n → Bool)
    (t allowedFailures : Nat)
    (hphase : UniformFinitePhase ring P.transition Domain
      (fun C => PopulationProtocol.IsSafe P ring C isLeader)
      safeTest t allowedFailures) :
    UniformFiniteHorizonSSLEOn P ring isLeader Domain
      t allowedFailures := by
  intro C hC
  have hphaseC := hphase.2 C hC
  have hcount := localHitCount_le_stabilizingScheduleCount
    P ring isLeader safeTest hphase.1 C t
  exact Nat.le_trans hphaseC (Nat.add_le_add_right hcount _)

/-- Main Definition-1 safety corollary on a closed domain.  Generic semantic
safety is already closed under reachability; the extra closure premise needed
for block reuse is exactly closure of `Domain`. -/
theorem boundedIsSafeProducer_repeatedBlockSSLEOn
    (P : PopulationProtocol) {n : Nat}
    (ring : DirectedRing n) (isLeader : P.Y → Bool)
    (Domain : P.Configuration n → Prop)
    (safeTest : P.Configuration n → Bool)
    (hdec : ∀ C, safeTest C = true ↔
      PopulationProtocol.IsSafe P ring C isLeader)
    (hDomainClosed : LocalStepClosed ring P.transition Domain)
    (L : Nat)
    (hproducer : BoundedSafeScheduleProducer
      ring P.transition Domain
      (fun C => PopulationProtocol.IsSafe P ring C isLeader) L) :
    ∀ k, UniformFiniteHorizonSSLEOn P ring isLeader Domain
      (k * L) ((n ^ L - 1) ^ k) := by
  intro k
  apply uniformFinitePhase_isSafe_to_SSLEOn
  exact boundedSafeProducer_repeatedBlockPhase
    ring P.transition Domain
    (fun C => PopulationProtocol.IsSafe P ring C isLeader)
    safeTest hdec hDomainClosed L hproducer k

/-- Exact finite `c/n`-failure Definition-1 theorem on the closed domain. -/
theorem boundedIsSafeProducer_oneOverNSSLEOn
    (P : PopulationProtocol) {n : Nat}
    (ring : DirectedRing n) (isLeader : P.Y → Bool)
    (Domain : P.Configuration n → Prop)
    (safeTest : P.Configuration n → Bool)
    (hdec : ∀ C, safeTest C = true ↔
      PopulationProtocol.IsSafe P ring C isLeader)
    (hDomainClosed : LocalStepClosed ring P.transition Domain)
    (L k c : Nat)
    (hproducer : BoundedSafeScheduleProducer
      ring P.transition Domain
      (fun C => PopulationProtocol.IsSafe P ring C isLeader) L)
    (hc : c < n) (horizonPos : 0 < k * L)
    (hbudget : (n ^ L - 1) ^ k ≤ c * n ^ (k * L - 1)) :
    UniformOneOverNFailureAtHorizonOn
      P ring isLeader Domain c (k * L) := by
  refine ⟨hc, horizonPos, ?_⟩
  have hgeom := boundedIsSafeProducer_repeatedBlockSSLEOn
    P ring isLeader Domain safeTest hdec hDomainClosed
    L hproducer k
  intro C hC
  exact Nat.le_trans (hgeom C hC)
    (Nat.add_le_add_left hbudget _)

/-- Fully explicit finite `1/n` Definition-1 bound on the closed domain.  The
only protocol-specific obligation left is the bounded producer from every
nonsafe domain state. -/
theorem boundedIsSafeProducer_explicitOneOverNSSLEOn
    (P : PopulationProtocol) {n : Nat}
    (ring : DirectedRing n) (isLeader : P.Y → Bool)
    (Domain : P.Configuration n → Prop)
    (safeTest : P.Configuration n → Bool)
    (hdec : ∀ C, safeTest C = true ↔
      PopulationProtocol.IsSafe P ring C isLeader)
    (hDomainClosed : LocalStepClosed ring P.transition Domain)
    (hn2 : 1 < n) (L : Nat) (hL : 0 < L)
    (hproducer : BoundedSafeScheduleProducer
      ring P.transition Domain
      (fun C => PopulationProtocol.IsSafe P ring C isLeader) L) :
    let k := (n - 1) * (n ^ L - 1) + 1
    UniformOneOverNFailureAtHorizonOn
      P ring isLeader Domain 1 (k * L) := by
  let k := (n - 1) * (n ^ L - 1) + 1
  have hk : 0 < k := by simp [k]
  exact boundedIsSafeProducer_oneOverNSSLEOn
    P ring isLeader Domain safeTest hdec hDomainClosed
    L k 1 hproducer hn2 (Nat.mul_pos hk hL)
    (by simpa using geometricMiss_oneOverN_budget ring hn2 L hL)

/-- If the domain is all configurations, the domain theorem specializes to
the repository's global finite-horizon SSLE statement. -/
theorem boundedIsSafeProducer_repeatedBlockSSLE
    (P : PopulationProtocol) {n : Nat}
    (ring : DirectedRing n) (isLeader : P.Y → Bool)
    (safeTest : P.Configuration n → Bool)
    (hdec : ∀ C, safeTest C = true ↔
      PopulationProtocol.IsSafe P ring C isLeader)
    (L : Nat)
    (hproducer : ∀ C : P.Configuration n,
      ¬ PopulationProtocol.IsSafe P ring C isLeader →
        ∃ word : DetSchedule n,
          word.length ≤ L ∧
            PopulationProtocol.IsSafe P ring
              (runLocalSchedule ring P.transition C word) isLeader) :
    ∀ k, UniformFiniteHorizonSSLE P ring isLeader
      (k * L) ((n ^ L - 1) ^ k) := by
  have hDomainClosed : LocalStepClosed ring P.transition
      (fun _ : P.Configuration n => True) := by
    intro C hC e
    trivial
  have hproducer' : BoundedSafeScheduleProducer
      ring P.transition (fun _ : P.Configuration n => True)
      (fun C => PopulationProtocol.IsSafe P ring C isLeader) L := by
    intro C hC hnot
    exact hproducer C hnot
  intro k C
  exact boundedIsSafeProducer_repeatedBlockSSLEOn
    P ring isLeader (fun _ : P.Configuration n => True)
    safeTest hdec hDomainClosed L hproducer' k C trivial

end PPLLClosedDomainSchedulerAmplificationSol
