import Leader.Wu.Birth.ResponderHazardResidence

/-! Same-word physical schedule adapter. Other edges may mutate the current
predecessor freely. Avoiding the resident site's outgoing edge is explicit;
it is not a stable-neighbor or frozen-environment assumption. -/

set_option autoImplicit false

namespace BirthResponderHazardSchedule

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLNoCheckBirthConditionTwoGeometry
  PPLLNoCheckBirthConditionTwoProtocol BirthMismatchDisposalProducer
  BirthResponderHazardFull BirthResponderHazardResidence

variable {n psi kappa tau : Nat}

def incomingCount (ring : DirectedRing n) (i : Fin n) : DetSchedule n → Nat
  | [] => 0
  | e :: es => if ring.rightNeighbor e = i then incomingCount ring i es + 1
      else incomingCount ring i es

/-- Extract actual then-current predecessor states from the same raw word,
using the full physical global transition between samples. -/
def actualIncomingStates (ring : DirectedRing n) (hpsi : 0 < psi) (kappa tau : Nat)
    (i : Fin n) : (Fin n → ExpiringAgentState psi kappa tau) → DetSchedule n →
      List (ExpiringAgentState psi kappa tau)
  | _, [] => []
  | C, e :: es =>
      let D := localStep ring (actionOneFullTransition hpsi kappa tau) C e
      let tail := actualIncomingStates ring hpsi kappa tau i D es
      if ring.rightNeighbor e = i then C e :: tail else tail

/-- A sticky, physical observation on the actual full ring execution.
Only a true incoming edge can record the right-stage event. -/
def ScheduleBreak (ring : DirectedRing n) (hpsi : 0 < psi) (kappa tau : Nat)
    (i : Fin n) : (Fin n → ExpiringAgentState psi kappa tau) → DetSchedule n → Prop
  | C, [] => (C i).core.erase.core.path = .bot
  | C, e :: es => (C i).core.erase.core.path = .bot ∨
      (ring.rightNeighbor e = i ∧ HostEvent hpsi kappa (C e).core.erase (C i).core.erase) ∨
      ScheduleBreak ring hpsi kappa tau i
        (localStep ring (actionOneFullTransition hpsi kappa tau) C e) es

attribute [local irreducible] actionOneFullTransition

theorem incoming_length (ring : DirectedRing n) (hpsi : 0 < psi) (kappa tau : Nat)
    (i : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau) (word : DetSchedule n) :
    (actualIncomingStates ring hpsi kappa tau i C word).length = incomingCount ring i word := by
  induction word generalizing C with
  | nil => rfl
  | cons e es ih =>
      simp only [actualIncomingStates, incomingCount]
      split <;> simp only [List.length_cons, ih]

/-- Exact final local state on the same raw schedule after deleting only
irrelevant samples, with the outgoing-edge restriction stated explicitly. -/
theorem incoming_run_eq (ring : DirectedRing n) (hpsi : 0 < psi) (kappa tau : Nat)
    (i : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau) (word : DetSchedule n)
    (havoid : ∀ e ∈ word, e ≠ i) :
    (runLocalSchedule ring (actionOneFullTransition hpsi kappa tau) C word) i =
      incomingRun hpsi kappa tau (C i) (actualIncomingStates ring hpsi kappa tau i C word) := by
  induction word generalizing C with
  | nil => rfl
  | cons e es ih =>
      have hei : i ≠ e := Ne.symm (havoid e (by simp))
      have htail : ∀ f ∈ es, f ≠ i := fun f hf => havoid f (by simp [hf])
      let D := localStep ring (actionOneFullTransition hpsi kappa tau) C e
      change (runLocalSchedule ring (actionOneFullTransition hpsi kappa tau) D es) i = _
      rw [ih D htail]
      by_cases hr : ring.rightNeighbor e = i
      · have hD : D i = (actionOneFullTransition hpsi kappa tau (C e) (C i)).2 := by
          simp only [D, localStep, hei, hr, if_false, if_true]
        simp only [actualIncomingStates, hr, if_true, incomingRun]
        rw [hD]
      · have hD : D i = C i := by
          simp only [D, localStep, hei, Ne.symm hr, if_false]
        simp only [actualIncomingStates, hr, if_false]
        rw [hD]

/-- The computed residence observer is realized by a literal physical
observation on that same schedule, including any intermediate clear/refill. -/
theorem residence_break_to_schedule (ring : DirectedRing n) (hpsi : 0 < psi) (kappa tau : Nat)
    (i : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau) (word : DetSchedule n)
    (havoid : ∀ e ∈ word, e ≠ i)
    (hb : ResidenceBreak hpsi kappa tau (C i)
      (actualIncomingStates ring hpsi kappa tau i C word)) :
    ScheduleBreak ring hpsi kappa tau i C word := by
  induction word generalizing C with
  | nil => exact hb
  | cons e es ih =>
      have hei : i ≠ e := Ne.symm (havoid e (by simp))
      have htail : ∀ f ∈ es, f ≠ i := fun f hf => havoid f (by simp [hf])
      let D := localStep ring (actionOneFullTransition hpsi kappa tau) C e
      change (C i).core.erase.core.path = .bot ∨
        (ring.rightNeighbor e = i ∧ HostEvent hpsi kappa (C e).core.erase (C i).core.erase) ∨
        ScheduleBreak ring hpsi kappa tau i D es
      by_cases hr : ring.rightNeighbor e = i
      · have hD : D i = (actionOneFullTransition hpsi kappa tau (C e) (C i)).2 := by
          simp only [D, localStep, hei, hr, if_false, if_true]
        simp only [actualIncomingStates, hr, if_true, ResidenceBreak] at hb
        rcases hb with hc | he | hb
        · exact Or.inl hc
        · exact Or.inr (Or.inl ⟨hr, he⟩)
        · apply Or.inr ∘ Or.inr
          apply ih D htail
          simpa only [hD] using hb
      · have hD : D i = C i := by
          simp only [D, localStep, hei, Ne.symm hr, if_false]
        simp only [actualIncomingStates, hr, if_false] at hb
        apply Or.inr ∘ Or.inr
        apply ih D htail
        simpa only [hD] using hb

/-- The schedule-side deterministic hazard producer. All other ring edges
and every predecessor mutation are unrestricted. The conclusion is local
residence termination, not extinction of a global source cohort. -/
theorem actual_word_forces_residence_break (ring : DirectedRing n) (hpsi : 0 < psi)
    (kappa tau : Nat) (i : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau)
    (word : DetSchedule n) (j bit : Nat)
    (hp : (C i).core.erase.core.path = .some j bit) (hj : j ≠ 0)
    (ha : (C i).core.path0Crossed = false)
    (havoid : ∀ e ∈ word, e ≠ i) (hhits : tau + 2 ≤ incomingCount ring i word) :
    ScheduleBreak ring hpsi kappa tau i C word := by
  apply residence_break_to_schedule ring hpsi kappa tau i C word havoid
  apply tau_add_two_services hpsi kappa tau (C i) _ j bit hp hj ha
  rw [incoming_length]
  exact hhits

end BirthResponderHazardSchedule

#print axioms BirthResponderHazardSchedule.incoming_run_eq
#print axioms BirthResponderHazardSchedule.residence_break_to_schedule
#print axioms BirthResponderHazardSchedule.actual_word_forces_residence_break
