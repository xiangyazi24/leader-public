import Init.Data.Nat.Log2
import Leader.AAFJ.SmallRings
import Leader.Wu.Birth.ShortDoneParameterChoice
import Leader.Wu.Scheduler.ClosedDomainAmplification

/-!
# Exact small members of the corrected protocol family

The large-ring parameter witness is unchanged.  Sizes one and two reuse
AAFJSmallRings; size three has a separate three-label protocol.
-/

set_option autoImplicit false

namespace Q11497FeasibilityAudit

private theorem smallFamily_log2_ge_one
    (m : Nat) (hm : 2 ≤ m) : 1 ≤ Nat.log2 m := by
  rw [Nat.log2_def, if_pos hm]
  omega

private theorem smallFamily_log2_ge_two
    (n : Nat) (hn : 4 ≤ n) : 2 ≤ Nat.log2 n := by
  have hhalf : 2 ≤ n / 2 := by omega
  have hlog := smallFamily_log2_ge_one (n / 2) hhalf
  rw [Nat.log2_def, if_pos (show 2 ≤ n by omega)]
  omega

private theorem psiChoice_of_le_three
    (n : Nat) (hn : n ≤ 3) : psiChoice n = n - 1 := by
  unfold psiChoice scale BirthShortDoneDispatcher.loglogScale
  apply Nat.min_eq_right
  omega

/-- The unchanged parameter witness has at least three labels for n ≥ 4.
The proof uses the logarithm recurrence, not finite testing over n. -/
theorem psiChoice_gt_two (n : Nat) (hn : 4 ≤ n) :
    2 < psiChoice n := by
  have hlog : 1 ≤ Nat.log2 (Nat.log2 n) :=
    smallFamily_log2_ge_one (Nat.log2 n)
      (smallFamily_log2_ge_two n hn)
  have hmin :
      3 ≤ Nat.min (Nat.log2 (Nat.log2 n) + 1 + 1) (n - 1) := by
    apply Nat.le_min.mpr
    constructor <;> omega
  unfold psiChoice scale BirthShortDoneDispatcher.loglogScale
  omega

/-- Exactly the three-agent size selects psi = 2. -/
theorem psiChoice_eq_two_iff (n : Nat) :
    psiChoice n = 2 ↔ n = 3 := by
  constructor
  · intro h
    by_cases hn : n ≤ 3
    · rw [psiChoice_of_le_three n hn] at h
      omega
    · have hgt := psiChoice_gt_two n (by omega)
      omega
  · intro hn
    subst n
    exact psiChoice_of_le_three 3 (by omega)

/-- This arithmetic statement includes n = 0; DirectedRing itself does not. -/
theorem psiChoice_lt_two_iff (n : Nat) :
    psiChoice n < 2 ↔ n ≤ 2 := by
  constructor
  · intro h
    by_cases hn : n ≤ 3
    · rw [psiChoice_of_le_three n hn] at h
      omega
    · have hgt := psiChoice_gt_two n (by omega)
      omega
  · intro hn
    rw [psiChoice_of_le_three n (by omega)]
    omega

end Q11497FeasibilityAudit

namespace SmallRingFamily

open AAFJSmallRings
open PPLLResearchFormulation
open PPLLTraceConvergence
open PPLLSchedulerBlocks
open PPLLClosedDomainSchedulerAmplificationSol

private theorem fin_three_cases (i : Fin 3) :
    i = 0 ∨ i = 1 ∨ i = 2 := by
  rcases i with ⟨i, hi⟩
  have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases h with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- Successor in the three-label cycle. -/
def threeNext (a : Fin 3) : Fin 3 :=
  ⟨(a.val + 1) % 3, Nat.mod_lt _ (by omega)⟩

theorem threeNext_three (a : Fin 3) :
    threeNext (threeNext (threeNext a)) = a := by
  rcases fin_three_cases a with rfl | rfl | rfl <;> rfl

/-- The initiator is unchanged; the responder receives its successor label. -/
def threeProtocol : PopulationProtocol where
  Q := Fin 3
  Y := Bool
  transition := fun a _ => (a, threeNext a)
  output := fun a => decide (a = 0)

def threeStateValues : List threeProtocol.Q :=
  ([0, 1, 2] : List (Fin 3))


theorem threeStateValues_complete (q : threeProtocol.Q) :
    q ∈ threeStateValues := by
  change q ∈ ([0, 1, 2] : List (Fin 3))
  rcases fin_three_cases q with rfl | rfl | rfl <;> decide


theorem threeStateValues_nodup : threeStateValues.Nodup := by
  change ([0, 1, 2] : List (Fin 3)).Nodup
  decide


/-- Together with completeness and Nodup, this is the exact local-state count. -/
theorem threeProtocol_state_count : threeStateValues.length = 3 := by
  rfl

/-- Every directed edge has successor labels, including the wraparound edge. -/
def ThreeAligned (C : threeProtocol.Configuration 3) : Prop :=
  C 1 = threeNext (C 0) ∧
  C 2 = threeNext (C 1) ∧
  C 0 = threeNext (C 2)

theorem threeAligned_edge
    (ring : DirectedRing 3) (C : threeProtocol.Configuration 3)
    (hC : ThreeAligned C) (e : Fin 3) :
    C (ring.rightNeighbor e) = threeNext (C e) := by
  rcases fin_three_cases e with rfl | rfl | rfl
  · simpa [DirectedRing.rightNeighbor] using hC.1
  · simpa [DirectedRing.rightNeighbor] using hC.2.1
  · simpa [DirectedRing.rightNeighbor] using hC.2.2

theorem threeProtocol_aligned_fixed
    (ring : DirectedRing 3) (C : threeProtocol.Configuration 3)
    (hC : ThreeAligned C) (e : Fin 3) :
    threeProtocol.step ring C e = C := by
  have hnext := threeAligned_edge ring C hC e
  funext i
  change
    (if i = e then C e
     else if i = ring.rightNeighbor e then threeNext (C e)
     else C i) = C i
  by_cases hi : i = e
  · subst i
    rw [if_pos rfl]
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      simp only [if_neg hi]
      exact hnext.symm
    · simp only [if_neg hi]
      exact if_neg hj


theorem threeProtocol_aligned_closed (ring : DirectedRing 3) :
    threeProtocol.ClosedPred ring ThreeAligned := by
  intro C hC C' hstep
  rcases hstep with ⟨e, rfl⟩
  rw [threeProtocol_aligned_fixed ring C hC e]
  exact hC

theorem threeProtocol_reachable_eq_of_aligned
    (ring : DirectedRing 3)
    (C C' : threeProtocol.Configuration 3)
    (hC : ThreeAligned C)
    (hreach : threeProtocol.Reachable ring C C') :
    C' = C := by
  induction hreach with
  | refl => rfl
  | step C1 C2 h01 h12 ih =>
      rcases h12 with ⟨e, rfl⟩
      rw [ih, threeProtocol_aligned_fixed ring C hC e]

/-- An aligned cycle contains label zero at exactly one site. -/
theorem threeProtocol_aligned_unique
    (C : threeProtocol.Configuration 3) (hC : ThreeAligned C) :
    ∃ i : Fin 3, threeProtocol.output (C i) = true ∧
      ∀ j : Fin 3, threeProtocol.output (C j) = true → j = i := by
  have h1 : C 1 = threeNext (C 0) := hC.1
  have h2 : C 2 = threeNext (threeNext (C 0)) :=
    hC.2.1.trans (congrArg threeNext h1)
  rcases fin_three_cases (C 0) with h0 | h0 | h0
  · refine ⟨0, ?_, ?_⟩
    · simp [threeProtocol, h0]
    · intro j hj
      rcases fin_three_cases j with rfl | rfl | rfl <;>
        simp [threeProtocol, h1, h2, h0, threeNext] at hj ⊢
  · refine ⟨2, ?_, ?_⟩
    · simp [threeProtocol, h2, h0, threeNext]
    · intro j hj
      rcases fin_three_cases j with rfl | rfl | rfl <;>
        simp [threeProtocol, h1, h2, h0, threeNext] at hj ⊢
  · refine ⟨1, ?_, ?_⟩
    · simp [threeProtocol, h1, h0, threeNext]
    · intro j hj
      rcases fin_three_cases j with rfl | rfl | rfl <;>
        simp [threeProtocol, h1, h2, h0, threeNext] at hj ⊢

/-- Alignment implies the framework's genuine Definition-1 safety. -/
theorem threeProtocol_isSafe_of_aligned
    (ring : DirectedRing 3) (C : threeProtocol.Configuration 3)
    (hC : ThreeAligned C) :
    threeProtocol.IsSafe ring C (fun y => y) := by
  constructor
  · exact threeProtocol_aligned_unique C hC
  · intro C' hreach i
    rw [threeProtocol_reachable_eq_of_aligned ring C C' hC hreach]

theorem threeProtocol_two_requests_aligned
    (ring : DirectedRing 3) (C : threeProtocol.Configuration 3) :
    ThreeAligned (runSchedule threeProtocol ring C [0, 1]) := by
  change
    threeNext (C 0) = threeNext (C 0) ∧
    threeNext (threeNext (C 0)) = threeNext (threeNext (C 0)) ∧
    C 0 = threeNext (threeNext (threeNext (C 0)))
  exact ⟨rfl, rfl, (threeNext_three (C 0)).symm⟩


/-- The same two requests reach semantic safety from every configuration. -/
theorem threeProtocol_two_requests_safe
    (ring : DirectedRing 3) (C : threeProtocol.Configuration 3) :
    threeProtocol.IsSafe ring
      (runSchedule threeProtocol ring C [0, 1]) (fun y => y) :=
  threeProtocol_isSafe_of_aligned ring _
    (threeProtocol_two_requests_aligned ring C)

private theorem three_output_constraints
    (a b c : Fin 3)
    (hz : a = 0 ∨ b = 0 ∨ c = 0)
    (h01 : decide (threeNext a = 0) = decide (b = 0))
    (h12 : decide (threeNext b = 0) = decide (c = 0))
    (h20 : decide (threeNext c = 0) = decide (a = 0)) :
    b = threeNext a ∧ c = threeNext b ∧ a = threeNext c := by
  rcases fin_three_cases a with rfl | rfl | rfl <;>
    rcases fin_three_cases b with rfl | rfl | rfl <;>
    rcases fin_three_cases c with rfl | rfl | rfl <;>
    simp [threeNext] at hz h01 h12 h20 ⊢

theorem threeProtocol_aligned_of_isSafe
    (ring : DirectedRing 3) (C : threeProtocol.Configuration 3)
    (hC : threeProtocol.IsSafe ring C (fun y => y)) :
    ThreeAligned C := by
  let c : Fin 3 → Fin 3 := C
  have h01 := hC.2 (threeProtocol.step ring C 0)
    (PopulationProtocol.OneStep.to_reachable ⟨0, rfl⟩) 1
  have h12 := hC.2 (threeProtocol.step ring C 1)
    (PopulationProtocol.OneStep.to_reachable ⟨1, rfl⟩) 2
  have h20 := hC.2 (threeProtocol.step ring C 2)
    (PopulationProtocol.OneStep.to_reachable ⟨2, rfl⟩) 0
  change decide (threeNext (c 0) = 0) = decide (c 1 = 0) at h01
  change decide (threeNext (c 1) = 0) = decide (c 2 = 0) at h12
  change decide (threeNext (c 2) = 0) = decide (c 0 = 0) at h20
  have hz : c 0 = 0 ∨ c 1 = 0 ∨ c 2 = 0 := by
    obtain ⟨i, hi, _⟩ := hC.1
    change decide (c i = 0) = true at hi
    have hi0 : c i = 0 := of_decide_eq_true hi
    rcases fin_three_cases i with rfl | rfl | rfl
    · exact Or.inl hi0
    · exact Or.inr (Or.inl hi0)
    · exact Or.inr (Or.inr hi0)
  exact three_output_constraints (c 0) (c 1) (c 2) hz h01 h12 h20


theorem threeProtocol_isSafe_iff_aligned
    (ring : DirectedRing 3) (C : threeProtocol.Configuration 3) :
    threeProtocol.IsSafe ring C (fun y => y) ↔ ThreeAligned C :=
  ⟨threeProtocol_aligned_of_isSafe ring C,
    threeProtocol_isSafe_of_aligned ring C⟩

def threeAlignedTest (C : threeProtocol.Configuration 3) : Bool :=
  let c : Fin 3 → Fin 3 := C
  decide (c 1 = threeNext (c 0) ∧
    c 2 = threeNext (c 1) ∧
    c 0 = threeNext (c 2))


theorem threeAlignedTest_decides (C : threeProtocol.Configuration 3) :
    threeAlignedTest C = true ↔ ThreeAligned C := by
  let c : Fin 3 → Fin 3 := C
  change
    decide (c 1 = threeNext (c 0) ∧
      c 2 = threeNext (c 1) ∧ c 0 = threeNext (c 2)) = true ↔
    (c 1 = threeNext (c 0) ∧
      c 2 = threeNext (c 1) ∧ c 0 = threeNext (c 2))
  simp only [decide_eq_true_eq]


/-- In particular, the test decides IsSafe itself, not just a sufficient set. -/
theorem threeAlignedTest_decides_isSafe
    (ring : DirectedRing 3) (C : threeProtocol.Configuration 3) :
    threeAlignedTest C = true ↔
      threeProtocol.IsSafe ring C (fun y => y) :=
  (threeAlignedTest_decides C).trans
    (threeProtocol_isSafe_iff_aligned ring C).symm

theorem threeProtocol_local_aligned_closed (ring : DirectedRing 3) :
    LocalStepClosed ring threeProtocol.transition ThreeAligned := by
  intro C hC e
  change ThreeAligned (threeProtocol.step ring C e)
  rw [threeProtocol_aligned_fixed ring C hC e]
  exact hC

/-- Absorption makes the prefix-hitting test also an endpoint test. -/
theorem threeProtocol_hits_iff_aligned_endpoint
    (ring : DirectedRing 3) (C : threeProtocol.Configuration 3)
    (word : DetSchedule 3) :
    hitsWithinLocal ring threeProtocol.transition threeAlignedTest C word =
        true ↔
      ThreeAligned (runSchedule threeProtocol ring C word) := by
  have h := hitsWithinLocal_iff_closed_endpoint
    ring threeProtocol.transition ThreeAligned threeAlignedTest
    threeAlignedTest_decides (threeProtocol_local_aligned_closed ring) C word
  rw [runLocalSchedule_eq_runSchedule threeProtocol ring C word] at h
  exact h

theorem threeProtocol_two_requests_hit
    (ring : DirectedRing 3) (C : threeProtocol.Configuration 3) :
    hitsWithinLocal ring threeProtocol.transition threeAlignedTest C
      [0, 1] = true :=
  (threeProtocol_hits_iff_aligned_endpoint ring C [0, 1]).2
    (threeProtocol_two_requests_aligned ring C)

/-- Exactly one of the nine two-letter outcomes is the distinguished word.
This is the only scheduler-enumeration calculation in this file. -/
theorem threeProtocol_favorable_pair_count :
    (allSchedules 3 2).length = 9 ∧
      (allSchedules 3 2).countP
        (fun s => decide (s = ([0, 1] : DetSchedule 3))) = 1 := by
  constructor
  · simpa using allSchedules_length 3 2
  · decide

/-- Every starting state has at most eight misses in one two-letter block. -/
theorem threeProtocol_one_block_miss_le
    (ring : DirectedRing 3) (C : threeProtocol.Configuration 3) :
    localMissCount ring threeProtocol.transition threeAlignedTest C 2 ≤ 8 := by
  have hpos :
      0 < localHitCount ring threeProtocol.transition threeAlignedTest C 2 := by
    unfold localHitCount
    apply List.countP_pos_iff.mpr
    exact ⟨[0, 1], mem_allSchedules_of_length 3 2 [0, 1] rfl,
      threeProtocol_two_requests_hit ring C⟩
  have hpart := localMissCount_add_localHitCount
    ring threeProtocol.transition threeAlignedTest C 2
  have hspace : (allSchedules 3 2).length = 9 :=
    threeProtocol_favorable_pair_count.1
  rw [hspace] at hpart
  omega

/-- Exact repeated-block bound.  The induction uses the list-product
composition theorem, which is uniform over all intermediate configurations. -/
theorem threeProtocol_missCount_blocks
    (ring : DirectedRing 3) (k : Nat) :
    ∀ C : threeProtocol.Configuration 3,
      localMissCount ring threeProtocol.transition threeAlignedTest C (2 * k) ≤
        8 ^ k := by
  induction k with
  | zero =>
      intro C
      have h :
          localMissCount ring threeProtocol.transition threeAlignedTest C 0 ≤
            (allSchedules 3 0).length :=
        List.countP_le_length
      simpa only [allSchedules_length, Nat.pow_zero, Nat.mul_zero] using h
  | succ k ih =>
      intro C
      have h := localMissCount_add_le_mul
        ring threeProtocol.transition threeAlignedTest
        (2 * k) 2 (8 ^ k) 8 ih (threeProtocol_one_block_miss_le ring) C
      simpa only [Nat.mul_succ, Nat.pow_succ] using h

/-- At horizon twenty the exact Boolean miss numerator is at most 8^10. -/
theorem threeProtocol_missCount_twenty
    (ring : DirectedRing 3) (C : threeProtocol.Configuration 3) :
    localMissCount ring threeProtocol.transition threeAlignedTest C 20 ≤
      8 ^ 10 :=
  threeProtocol_missCount_blocks ring 10 C

/-- The requested integer tail in the generic local finite scheduler. -/
theorem threeProtocol_twenty_local_tail
    (ring : DirectedRing 3) (C : threeProtocol.Configuration 3) :
    3 * localMissCount ring threeProtocol.transition threeAlignedTest C 20 ≤
      3 ^ 20 := by
  exact Nat.le_trans
    (Nat.mul_le_mul_left 3 (threeProtocol_missCount_twenty ring C))
    (by decide : 3 * 8 ^ 10 ≤ (3 : Nat) ^ 20)

/-- Bridge to the repository's semantic Definition-1 safety count, with the
stronger geometric allowed-failure budget 8^10. -/
theorem threeProtocol_twenty_safe_count (ring : DirectedRing 3) :
    UniformFiniteHorizonSSLE threeProtocol ring (fun y => y) 20 (8 ^ 10) := by
  intro C
  have hmiss := threeProtocol_missCount_twenty ring C
  have hpart := localMissCount_add_localHitCount
    ring threeProtocol.transition threeAlignedTest C 20
  have hhit := localHitCount_le_stabilizingScheduleCount
    threeProtocol ring (fun y => y) threeAlignedTest
    (threeAlignedTest_decides_isSafe ring) C 20
  omega

/-- Here the subtracted count is precisely the repository's count of words
that reach IsSafe at some prefix.  Hence the difference is the number of
20-letter outcomes missing semantic safety. -/
theorem threeProtocol_twenty_tail
    (ring : DirectedRing 3) (C : threeProtocol.Configuration 3) :
    3 * ((allSchedules 3 20).length -
      stabilizingScheduleCount threeProtocol ring (fun y => y) C 20) ≤
        3 ^ 20 := by
  have hgood := threeProtocol_twenty_safe_count ring C
  have hbad :
      (allSchedules 3 20).length -
        stabilizingScheduleCount threeProtocol ring (fun y => y) C 20 ≤
          8 ^ 10 := by
    omega
  exact Nat.le_trans (Nat.mul_le_mul_left 3 hbad)
    (by decide : 3 * 8 ^ 10 ≤ (3 : Nat) ^ 20)

/-- The repository's equivalent exact one-over-n formulation: c=1, n=3,
t=20.  No asymptotic or large-ring conclusion is asserted. -/
theorem threeProtocol_twenty_oneOverN (ring : DirectedRing 3) :
    UniformOneOverNFailureAtHorizon threeProtocol ring (fun y => y) 1 20 := by
  refine ⟨by decide, by decide, ?_⟩
  intro C
  have h := threeProtocol_twenty_safe_count ring C
  have hbudget : 8 ^ 10 ≤ 1 * (3 : Nat) ^ (20 - 1) := by
    decide
  exact Nat.le_trans h (Nat.add_le_add_left hbudget _)

/-- Separate exact-size protocols.  The zero case is a harmless value making
the function total on the requested arithmetic domain; no DirectedRing 0
exists, and no safety theorem below claims otherwise. -/
def smallFamilyMember (n : Nat) (_hn : n ≤ 3) : PopulationProtocol :=
  match n with
  | 0 => oneProtocol
  | 1 => oneProtocol
  | 2 => twoProtocol
  | _ + 3 => threeProtocol

/-- Every selected member uses Bool outputs with the identity leader test. -/
def smallFamilyIsLeader :
    (n : Nat) → (hn : n ≤ 3) → (smallFamilyMember n hn).Y → Bool
  | 0, _ => id
  | 1, _ => id
  | 2, _ => id
  | _ + 3, _ => id

/-- Each positive small member has exactly n local states, presented by a
complete duplicate-free list as in AAFJSmallRings. -/
theorem smallFamilyMember_state_count
    (n : Nat) (hn : n ≤ 3) (ring : DirectedRing n) :
    ∃ values : List (smallFamilyMember n hn).Q,
      values.Nodup ∧
      (∀ q : (smallFamilyMember n hn).Q, q ∈ values) ∧
      values.length = n := by
  have hcases : n = 1 ∨ n = 2 ∨ n = 3 := by
    have hpos := ring.hn
    omega
  rcases hcases with rfl | rfl | rfl
  · exact ⟨oneStateValues, oneStateValues_nodup,
      oneStateValues_complete, oneStateValues_length⟩
  · exact ⟨twoStateValues, twoStateValues_nodup,
      twoStateValues_complete, twoStateValues_length⟩
  · exact ⟨threeStateValues, threeStateValues_nodup,
      threeStateValues_complete, threeProtocol_state_count⟩

/-- A single word, chosen independently of the initial configuration, reaches
Definition-1 safety for each small member.  The words are [], [0], [0,1]. -/
theorem smallFamilyMember_safe
    (n : Nat) (hn : n ≤ 3) (ring : DirectedRing n) :
    ∃ word : DetSchedule n, word.length ≤ 2 ∧
      ∀ C : (smallFamilyMember n hn).Configuration n,
        (smallFamilyMember n hn).IsSafe ring
          (runSchedule (smallFamilyMember n hn) ring C word)
          (smallFamilyIsLeader n hn) := by
  have hcases : n = 1 ∨ n = 2 ∨ n = 3 := by
    have hpos := ring.hn
    omega
  rcases hcases with rfl | rfl | rfl
  · refine ⟨[], by decide, ?_⟩
    intro C
    exact oneProtocol_isSafe ring C
  · refine ⟨[0], by decide, ?_⟩
    intro C
    exact twoProtocol_one_step_isSafe ring C 0
  · refine ⟨[0, 1], by decide, ?_⟩
    intro C
    exact threeProtocol_two_requests_safe ring C

/-- Safety is closed for every selected small member. -/
theorem smallFamilyMember_safe_closed
    (n : Nat) (hn : n ≤ 3) (ring : DirectedRing n) :
    (smallFamilyMember n hn).ClosedPred ring
      (fun C => (smallFamilyMember n hn).IsSafe ring C
        (smallFamilyIsLeader n hn)) :=
  isSafe_closed (smallFamilyMember n hn) ring (smallFamilyIsLeader n hn)

/-- Named downstream wiring obligation for an all-size family.  It requires
both the actual protocol member and the designated output test to agree.
This is a proposition, not an added axiom and not a premise of any theorem
above.  It says nothing about correctness of the large-ring branch. -/
def SmallFamilyAssemblyObligation
    (family : Nat → PopulationProtocol)
    (isLeader : (n : Nat) → (family n).Y → Bool) : Prop :=
  ∀ (n : Nat) (hn : n ≤ 3), 0 < n →
    family n = smallFamilyMember n hn ∧
      HEq (isLeader n) (smallFamilyIsLeader n hn)

/-!
ASSEMBLY OBLIGATION: SmallFamilyAssemblyObligation must be instantiated for
the actual final all-size family.  Its n ≥ 4 branch must separately supply
the composed protocol's safety, runtime/scheduler, and state-count theorems;
psiChoice_gt_two supplies only the additional numeric parameter premise.
The final theorem must then combine that branch with these small members.

Nothing here claims to discharge the physical consumer's small-ring birth
wrapper or a B9/R1 lifecycle obligation by changing parameters in that row.
-/

end SmallRingFamily
