import Leader.Wu.Birth.ResponderHazardMassCount
import Leader.Wu.Birth.ResponderHazardSchedule

/-!
# Actual finite uniform mass for old-host responder residence termination

The sampled words are the original `allSchedules` enumeration. The favorable
cylinder is proved to have sufficient mass; avoiding the outgoing edge is no
longer a premise about the sampled word. Every intermediate configuration is
the actual old-host physical configuration. This is not global GEN extinction
and does not apply automatically to the latest SingleUse25 transition.
-/

set_option autoImplicit false

namespace BirthResponderHazardMass

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLNoCheckBirthConditionTwoGeometry
  PPLLNoCheckBirthConditionTwoProtocol PPLLSchedulerBlocks
  BirthMismatchDisposalProducer BirthResponderHazardFull
  BirthResponderHazardSchedule BirthResponderHazardResidence BirthResponderHazardMassArithmetic
  BirthResponderHazardMassCount

variable {n psi kappa tau : Nat}

private theorem right_left (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val = 0
  · rw [hi]
    have hlt : n - 1 < n := by have hn := ring.hn; omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    rw [show n - 1 + 1 = n by have hn := ring.hn; omega, Nat.mod_self]
  · have heq : i.val + n - 1 = n + (i.val - 1) := by omega
    have hmod : (n + (i.val - 1)) % n = i.val - 1 := by
      simp [Nat.mod_eq_of_lt (by omega : i.val - 1 < n)]
    rw [heq, hmod]
    rw [show i.val - 1 + 1 = i.val by omega, Nat.mod_eq_of_lt i.isLt]

/-- The actual incoming and outgoing scheduler letters are distinct. -/
theorem incoming_outgoing_distinct (ring : DirectedRing n) (hn : 2 ≤ n) (i : Fin n) :
    ring.leftNeighbor i ≠ i := by
  intro he
  have hh := right_left ring i
  rw [he] at hh
  exact rightNeighbor_ne_self_of_one_lt ring (by omega) i hh

theorem blockGood_spec (a b : Fin n) (w : DetSchedule n) (hg : blockGood a b w = true) :
    (∀ e ∈ w, e ≠ b) ∧ a ∈ w := by
  have hh : w.all (allowOne b) = true ∧ (!(w.all (allowOne a))) = true := by
    simpa only [blockGood, Bool.and_eq_true] using hg
  have ha : ∀ e ∈ w, e ≠ b := by
    intro e he
    have hx := List.all_eq_true.mp hh.1 e he
    simpa only [allowOne, decide_eq_true_eq] using hx
  refine ⟨ha, ?_⟩
  by_cases hm : a ∈ w
  · exact hm
  · have hall : w.all (allowOne a) = true := by
      apply List.all_eq_true.mpr
      intro e he
      apply decide_eq_true
      intro hea
      exact hm (hea ▸ he)
    have hnot := hh.2
    simp [hall] at hnot

private theorem incomingCount_append (ring : DirectedRing n) (i : Fin n)
    (pre suf : DetSchedule n) :
    incomingCount ring i (pre ++ suf) = incomingCount ring i pre + incomingCount ring i suf := by
  induction pre with
  | nil => simp [incomingCount]
  | cons e es ih =>
      simp only [List.cons_append, incomingCount]
      split <;> rw [ih] <;> omega

private theorem incomingCount_pos (ring : DirectedRing n) (i a : Fin n)
    (word : DetSchedule n) (ha : ring.rightNeighbor a = i) (hm : a ∈ word) :
    1 ≤ incomingCount ring i word := by
  induction word with
  | nil => simp at hm
  | cons e es ih =>
      rcases List.mem_cons.mp hm with he | hm
      · subst e
        simp [incomingCount, ha]
      · have ht := ih hm
        simp only [incomingCount]
        split <;> omega

/-- Every favorable whole word meets the two concrete hypotheses of the
already-checked physical schedule theorem. -/
theorem cylinder_service (ring : DirectedRing n) (i a : Fin n)
    (ha : ring.rightNeighbor a = i) (blocks : Nat) (word : DetSchedule n)
    (hg : cylinder n (blockGood a i) blocks word = true) :
    (∀ e ∈ word, e ≠ i) ∧ blocks ≤ incomingCount ring i word := by
  induction blocks generalizing word with
  | zero =>
      have he : word = [] := List.isEmpty_iff.mp hg
      subst word
      simp [incomingCount]
  | succ blocks ih =>
      have hh : blockGood a i (word.take n) = true ∧
          cylinder n (blockGood a i) blocks (word.drop n) = true := by
        simpa only [cylinder, Bool.and_eq_true] using hg
      have hp := blockGood_spec a i (word.take n) hh.1
      have ht := ih (word.drop n) hh.2
      refine ⟨?_, ?_⟩
      · intro e he
        rw [← List.take_append_drop n word] at he
        rcases List.mem_append.mp he with he | he
        · exact hp.1 e he
        · exact ht.1 e he
      · have hc := incomingCount_pos ring i a (word.take n) ha hp.2
        have he := incomingCount_append ring i (word.take n) (word.drop n)
        rw [List.take_append_drop] at he
        omega

/-- Executable Boolean observation of the exact already-checked predicate.
The recursive call follows the actual physical successor. -/
def breakTest (ring : DirectedRing n) (hpsi : 0 < psi) (kappa tau : Nat) (i : Fin n) :
    (Fin n → ExpiringAgentState psi kappa tau) → DetSchedule n → Bool
  | C, [] => decide ((C i).core.erase.core.path = .bot)
  | C, e :: es => decide ((C i).core.erase.core.path = .bot) ||
      (decide (ring.rightNeighbor e = i) &&
        decide (HostEvent hpsi kappa (C e).core.erase (C i).core.erase)) ||
      breakTest ring hpsi kappa tau i
        (localStep ring (actionOneFullTransition hpsi kappa tau) C e) es

theorem breakTest_iff (ring : DirectedRing n) (hpsi : 0 < psi) (kappa tau : Nat)
    (i : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau) (word : DetSchedule n) :
    breakTest ring hpsi kappa tau i C word = true ↔ ScheduleBreak ring hpsi kappa tau i C word := by
  induction word generalizing C with
  | nil => simp [breakTest, ScheduleBreak]
  | cons e es ih =>
      simp only [breakTest, ScheduleBreak, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq, ih, or_assoc]

private theorem scheduleBreak_of_empty (ring : DirectedRing n) (hpsi : 0 < psi) (kappa tau : Nat)
    (i : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau) (word : DetSchedule n)
    (hp : (C i).core.erase.core.path = .bot) : ScheduleBreak ring hpsi kappa tau i C word := by
  cases word
  · exact hp
  · exact Or.inl hp

/-- A recorded physical event survives arbitrary suffix padding. The
configuration itself still evolves by the real host during the suffix. -/
theorem scheduleBreak_padding (ring : DirectedRing n) (hpsi : 0 < psi) (kappa tau : Nat)
    (i : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau) (pre suf : DetSchedule n)
    (hp : ScheduleBreak ring hpsi kappa tau i C pre) :
    ScheduleBreak ring hpsi kappa tau i C (pre ++ suf) := by
  induction pre generalizing C with
  | nil => exact scheduleBreak_of_empty ring hpsi kappa tau i C suf hp
  | cons e es ih =>
      rcases hp with hc | he | ht
      · exact Or.inl hc
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr (ih _ ht))

/-- The endpoint remains the exact retained physical successor under that
same padding, even after the residence observation has become true. -/
theorem actual_padding_endpoint (ring : DirectedRing n) (hpsi : 0 < psi) (kappa tau : Nat)
    (C : Fin n → ExpiringAgentState psi kappa tau) (pre suf : DetSchedule n) :
    runLocalSchedule ring (actionOneFullTransition hpsi kappa tau) C (pre ++ suf) =
      runLocalSchedule ring (actionOneFullTransition hpsi kappa tau)
        (runLocalSchedule ring (actionOneFullTransition hpsi kappa tau) C pre) suf :=
  runLocalSchedule_append ring _ C pre suf

def breakCount (ring : DirectedRing n) (hpsi : 0 < psi) (kappa tau : Nat)
    (i : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau) (T : Nat) : Nat :=
  (allSchedules n T).countP (breakTest ring hpsi kappa tau i C)

def breakProbability (ring : DirectedRing n) (hpsi : 0 < psi) (kappa tau : Nat)
    (i : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau) (T : Nat) : Rat :=
  (breakCount ring hpsi kappa tau i C T : Rat) / (n ^ T : Nat)

/-- Exact favorable-cylinder count is dominated by actual physical success
count on the same raw words. The service budget comes from the current
physical timer, and every predecessor is the one produced by the raw word. -/
theorem cylinder_le_physical_count_of_budget (ring : DirectedRing n) (hn : 2 ≤ n)
    (hpsi : 0 < psi) (kappa tau : Nat) (i : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (j bit blocks : Nat)
    (hp : (C i).core.erase.core.path = .some j bit) (hj : j ≠ 0)
    (ha : (C i).core.path0Crossed = false) (hbudget : (C i).stall.val + 2 ≤ blocks) :
    blockNumerator n ^ blocks ≤ breakCount ring hpsi kappa tau i C (n * blocks) := by
  rw [← good_cylinder_count (ring.leftNeighbor i) i (incoming_outgoing_distinct ring hn i) hn]
  apply List.countP_mono_left
  intro word _ hg
  have hs := cylinder_service ring i (ring.leftNeighbor i) (right_left ring i) blocks word hg
  apply (breakTest_iff ring hpsi kappa tau i C word).mpr
  apply residence_break_to_schedule ring hpsi kappa tau i C word hs.1
  apply incoming_services_force_break hpsi kappa tau (C i) _ j bit hp hj ha
  rw [incoming_length]
  exact Nat.le_trans hbudget hs.2

/-- The type's actual timer cap supplies the uniform budget. No no-birth,
fixed-neighbor, or fair-stream premise is introduced. -/
theorem cylinder_le_physical_count (ring : DirectedRing n) (hn : 2 ≤ n)
    (hpsi : 0 < psi) (kappa tau : Nat) (i : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (j bit : Nat)
    (hp : (C i).core.erase.core.path = .some j bit) (hj : j ≠ 0)
    (ha : (C i).core.path0Crossed = false) :
    blockNumerator n ^ (tau + 2) ≤ breakCount ring hpsi kappa tau i C (n * (tau + 2)) := by
  apply cylinder_le_physical_count_of_budget ring hn hpsi kappa tau i C j bit (tau + 2) hp hj ha
  have ht := (C i).stall.isLt
  omega

/-- The sharper horizon and exponent use the actual initial timer value. -/
theorem current_timer_mass (ring : DirectedRing n) (hn : 2 ≤ n) (hpsi : 0 < psi)
    (kappa tau : Nat) (i : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau)
    (j bit : Nat) (hp : (C i).core.erase.core.path = .some j bit) (hj : j ≠ 0)
    (ha : (C i).core.path0Crossed = false) :
    n ^ (n * ((C i).stall.val + 2)) ≤ 8 ^ ((C i).stall.val + 2) *
      breakCount ring hpsi kappa tau i C (n * ((C i).stall.val + 2)) :=
  Nat.le_trans (repeated_block_eighth n ((C i).stall.val + 2) hn)
    (Nat.mul_le_mul_left _ (cylinder_le_physical_count_of_budget ring hn hpsi kappa tau i C j bit
      ((C i).stall.val + 2) hp hj ha (Nat.le_refl _)))

/-- Division-free unconditional uniform-word mass. Outgoing avoidance is a
proved favorable subset, not a premise about the uniform scheduler. -/
theorem physical_mass (ring : DirectedRing n) (hn : 2 ≤ n) (hpsi : 0 < psi)
    (kappa tau : Nat) (i : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau)
    (j bit : Nat) (hp : (C i).core.erase.core.path = .some j bit) (hj : j ≠ 0)
    (ha : (C i).core.path0Crossed = false) :
    n ^ (n * (tau + 2)) ≤ 8 ^ (tau + 2) *
      breakCount ring hpsi kappa tau i C (n * (tau + 2)) :=
  Nat.le_trans (repeated_block_eighth n (tau + 2) hn)
    (Nat.mul_le_mul_left _ (cylinder_le_physical_count ring hn hpsi kappa tau i C j bit hp hj ha))

private theorem inverse_le_fraction (Q N K : Nat) (hQ : 0 < Q) (hN : 0 < N)
    (h : N ≤ Q * K) : (1 : Rat) / (Q : Nat) ≤ (K : Rat) / (N : Nat) := by
  have hQ' : (0 : Rat) < (Q : Nat) := Rat.natCast_pos.mpr hQ
  have hN' : (0 : Rat) < (N : Nat) := Rat.natCast_pos.mpr hN
  apply Rat.le_of_mul_le_mul_right (c := (N : Rat))
  · rw [Rat.div_mul_cancel (Rat.ne_of_lt hN').symm]
    apply Rat.le_of_mul_le_mul_right (c := (Q : Rat))
    · have he : ((1 : Rat) / (Q : Nat) * (N : Nat)) * (Q : Nat) = (N : Nat) := by
        calc
          ((1 : Rat) / (Q : Nat) * (N : Nat)) * (Q : Nat) =
              ((1 : Rat) / (Q : Nat) * (Q : Nat)) * (N : Nat) := by
                rw [Rat.mul_assoc, Rat.mul_comm (N : Rat) (Q : Rat), ← Rat.mul_assoc]
          _ = (N : Nat) := by rw [Rat.div_mul_cancel (Rat.ne_of_lt hQ').symm, Rat.one_mul]
      rw [he, ← Rat.natCast_mul, Rat.natCast_le_natCast]
      simpa only [Nat.mul_comm] using h
    · exact hQ'
  · exact hN'

/-- At the real horizon `n*(tau+2)`, the exact rational probability of a
computed local residence break is at least `8^(-(tau+2))`. This does not claim
a lower bound on birth probability or loss of an entire source cohort. -/
theorem physical_probability (ring : DirectedRing n) (hn : 2 ≤ n) (hpsi : 0 < psi)
    (kappa tau : Nat) (i : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau)
    (j bit : Nat) (hp : (C i).core.erase.core.path = .some j bit) (hj : j ≠ 0)
    (ha : (C i).core.path0Crossed = false) :
    (1 : Rat) / (8 : Rat) ^ (tau + 2) ≤
      breakProbability ring hpsi kappa tau i C (n * (tau + 2)) := by
  have h := inverse_le_fraction (8 ^ (tau + 2)) (n ^ (n * (tau + 2)))
    (breakCount ring hpsi kappa tau i C (n * (tau + 2)))
    (Nat.pow_pos (by decide)) (Nat.pow_pos ring.hn)
    (physical_mass ring hn hpsi kappa tau i C j bit hp hj ha)
  simpa only [breakProbability, Rat.natCast_pow, Rat.natCast_ofNat] using h

/-- Exact finite uniform mass with the exponent read from the initial
physical state; the runtime timer cap is not changed. -/
theorem current_timer_probability (ring : DirectedRing n) (hn : 2 ≤ n) (hpsi : 0 < psi)
    (kappa tau : Nat) (i : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau)
    (j bit : Nat) (hp : (C i).core.erase.core.path = .some j bit) (hj : j ≠ 0)
    (ha : (C i).core.path0Crossed = false) :
    (1 : Rat) / (8 : Rat) ^ ((C i).stall.val + 2) ≤
      breakProbability ring hpsi kappa tau i C (n * ((C i).stall.val + 2)) := by
  have h := inverse_le_fraction (8 ^ ((C i).stall.val + 2)) (n ^ (n * ((C i).stall.val + 2)))
    (breakCount ring hpsi kappa tau i C (n * ((C i).stall.val + 2)))
    (Nat.pow_pos (by decide)) (Nat.pow_pos ring.hn)
    (current_timer_mass ring hn hpsi kappa tau i C j bit hp hj ha)
  simpa only [breakProbability, Rat.natCast_pow, Rat.natCast_ofNat] using h

end BirthResponderHazardMass

#print axioms BirthResponderHazardMass.incoming_outgoing_distinct
#print axioms BirthResponderHazardMass.cylinder_service
#print axioms BirthResponderHazardMass.breakTest_iff
#print axioms BirthResponderHazardMass.scheduleBreak_padding
#print axioms BirthResponderHazardMass.actual_padding_endpoint
#print axioms BirthResponderHazardMass.cylinder_le_physical_count
#print axioms BirthResponderHazardMass.physical_mass
#print axioms BirthResponderHazardMass.physical_probability

#print axioms BirthResponderHazardMass.cylinder_le_physical_count_of_budget
#print axioms BirthResponderHazardMass.current_timer_mass
#print axioms BirthResponderHazardMass.current_timer_probability
