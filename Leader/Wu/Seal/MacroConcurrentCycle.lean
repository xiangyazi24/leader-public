import Leader.Wu.Safety.CorrectedFormulation

/-!
# A six-site concurrent cycle for an abstract seal sweep

This file studies only the four-state macro rule displayed below.  It does not
claim that the states or transitions are implemented by `P_partial`.

The states record leader/follower (`L`/`F`) and sealed/unsealed (`S`/`U`).
Under the round-robin edge word `0,1,2,3,4,5`, the configuration

`FU, FS, LU, FS, LU, FS`

returns to itself after six genuine state-changing interactions.  Every
intermediate configuration still has leaders at positions two and four.
Repeating the word selects every directed edge infinitely often, so it gives
an explicit edge-fair infinite execution which never reaches a safe
unique-leader configuration for this abstract protocol.
-/

namespace SealSweepConcurrentCycleSol

open PPLLResearchFormulation

/-! ## Four-state macro protocol -/

inductive SealMacroState where
  | LS
  | FS
  | LU
  | FU
deriving DecidableEq, Repr

open SealMacroState

def sealMacroOutput : SealMacroState → Bool
  | LS | LU => true
  | FS | FU => false

/-- The exact ordered current-pair rule under audit.  Every pair not listed
here is identity. -/
def sealMacroTransition :
    SealMacroState → SealMacroState →
      SealMacroState × SealMacroState
  | LS, FS => (LU, FU)
  | FU, FS => (FS, FU)
  | FU, LS => (FS, FU)
  | FU, LU => (FS, LS)
  | LS, LS => (LS, FS)
  | l, r => (l, r)

def sealMacroProtocol : PopulationProtocol where
  Q := SealMacroState
  Y := Bool
  transition := sealMacroTransition
  output := sealMacroOutput

abbrev SealMacroConfig (n : Nat) :=
  sealMacroProtocol.Configuration n

private theorem ringSix : DirectedRing 6 :=
  ⟨by omega⟩

/-! ## The exact six-step cycle -/

/-- Initial word `FU, FS, LU, FS, LU, FS`. -/
def cycleC0 : SealMacroConfig 6 := fun i =>
  match i.val with
  | 0 => FU
  | 1 => FS
  | 2 => LU
  | 3 => FS
  | 4 => LU
  | _ => FS

/-- Successive configurations after edges zero through four. -/
def cycleC1 : SealMacroConfig 6 :=
  sealMacroProtocol.step ringSix cycleC0 0

def cycleC2 : SealMacroConfig 6 :=
  sealMacroProtocol.step ringSix cycleC1 1

def cycleC3 : SealMacroConfig 6 :=
  sealMacroProtocol.step ringSix cycleC2 2

def cycleC4 : SealMacroConfig 6 :=
  sealMacroProtocol.step ringSix cycleC3 3

def cycleC5 : SealMacroConfig 6 :=
  sealMacroProtocol.step ringSix cycleC4 4

def cycleC6 : SealMacroConfig 6 :=
  sealMacroProtocol.step ringSix cycleC5 5

private theorem finSix_cases (i : Fin 6) :
    i = (0 : Fin 6) ∨ i = (1 : Fin 6) ∨ i = (2 : Fin 6) ∨
      i = (3 : Fin 6) ∨ i = (4 : Fin 6) ∨ i = (5 : Fin 6) := by
  by_cases h0 : i.val = 0
  · left
    exact Fin.ext h0
  by_cases h1 : i.val = 1
  · right
    left
    exact Fin.ext h1
  by_cases h2 : i.val = 2
  · right
    right
    left
    exact Fin.ext h2
  by_cases h3 : i.val = 3
  · right
    right
    right
    left
    exact Fin.ext h3
  by_cases h4 : i.val = 4
  · right
    right
    right
    right
    left
    exact Fin.ext h4
  · right
    right
    right
    right
    right
    apply Fin.ext
    omega

theorem cycle_step_zero :
    sealMacroProtocol.step ringSix cycleC0 0 = cycleC1 := by
  rfl

theorem cycle_step_one :
    sealMacroProtocol.step ringSix cycleC1 1 = cycleC2 := by
  rfl

theorem cycle_step_two :
    sealMacroProtocol.step ringSix cycleC2 2 = cycleC3 := by
  rfl

theorem cycle_step_three :
    sealMacroProtocol.step ringSix cycleC3 3 = cycleC4 := by
  rfl

theorem cycle_step_four :
    sealMacroProtocol.step ringSix cycleC4 4 = cycleC5 := by
  rfl

theorem cycle_step_five :
    sealMacroProtocol.step ringSix cycleC5 5 = cycleC0 := by
  change cycleC6 = cycleC0
  funext i
  rcases finSix_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The literal edge word for one period. -/
def cycleWord : List (Fin 6) := [0, 1, 2, 3, 4, 5]

theorem cycleWord_length : cycleWord.length = 6 := by
  rfl

/-- Executing one complete round returns exactly to the starting word. -/
theorem run_cycleWord_eq :
    runSchedule sealMacroProtocol ringSix cycleC0 cycleWord = cycleC0 := by
  change cycleC6 = cycleC0
  exact cycle_step_five

/-! ## Two leaders throughout the period -/

def MacroHasTwoLeaders (C : SealMacroConfig 6) : Prop :=
  ∃ i j : Fin 6, i ≠ j ∧
    sealMacroOutput (C i) = true ∧
    sealMacroOutput (C j) = true

private theorem finSix_two_ne_four : (2 : Fin 6) ≠ (4 : Fin 6) := by
  decide

theorem cycleC0_hasTwo : MacroHasTwoLeaders cycleC0 := by
  exact ⟨2, 4, finSix_two_ne_four, rfl, rfl⟩

theorem cycleC1_hasTwo : MacroHasTwoLeaders cycleC1 := by
  exact ⟨2, 4, finSix_two_ne_four, rfl, rfl⟩

theorem cycleC2_hasTwo : MacroHasTwoLeaders cycleC2 := by
  exact ⟨2, 4, finSix_two_ne_four, rfl, rfl⟩

theorem cycleC3_hasTwo : MacroHasTwoLeaders cycleC3 := by
  exact ⟨2, 4, finSix_two_ne_four, rfl, rfl⟩

theorem cycleC4_hasTwo : MacroHasTwoLeaders cycleC4 := by
  exact ⟨2, 4, finSix_two_ne_four, rfl, rfl⟩

theorem cycleC5_hasTwo : MacroHasTwoLeaders cycleC5 := by
  exact ⟨2, 4, finSix_two_ne_four, rfl, rfl⟩

theorem macroHasTwo_not_unique
    {C : SealMacroConfig 6} (htwo : MacroHasTwoLeaders C) :
    ¬ UniqueLeaderOutput sealMacroProtocol 6 C id := by
  rintro ⟨root, _, honly⟩
  obtain ⟨i, j, hij, hi, hj⟩ := htwo
  have hir : i = root := honly i hi
  have hjr : j = root := honly j hj
  exact hij (hir.trans hjr.symm)

/-! ## Periodic edge-fair infinite execution -/

/-- Every directed edge is selected infinitely often.  Since every ring edge
is always available in this macro semantics, this is the relevant weak
edge-fairness condition. -/
def WeakEdgeFair (schedule : Nat → Fin 6) : Prop :=
  ∀ e : Fin 6, ∀ t : Nat,
    ∃ u : Nat, t ≤ u ∧ schedule u = e

def roundRobinSchedule (t : Nat) : Fin 6 :=
  ⟨t % 6, Nat.mod_lt _ (by omega)⟩

theorem roundRobinSchedule_fair :
    WeakEdgeFair roundRobinSchedule := by
  intro e t
  refine ⟨6 * t + e.val, ?_, ?_⟩
  · omega
  · apply Fin.ext
    change (6 * t + e.val) % 6 = e.val
    omega

/-- Periodic state trajectory, indexed by the phase of the six-edge word. -/
def cycleExecution (t : Nat) : SealMacroConfig 6 :=
  match t % 6 with
  | 0 => cycleC0
  | 1 => cycleC1
  | 2 => cycleC2
  | 3 => cycleC3
  | 4 => cycleC4
  | _ => cycleC5

private theorem modSix_cases (t : Nat) :
    t % 6 = 0 ∨ t % 6 = 1 ∨ t % 6 = 2 ∨
      t % 6 = 3 ∨ t % 6 = 4 ∨ t % 6 = 5 := by
  have hlt : t % 6 < 6 := Nat.mod_lt _ (by omega)
  omega

theorem cycleExecution_initial : cycleExecution 0 = cycleC0 := by
  rfl

/-- Each successive trajectory state is the result of the scheduled exact
protocol interaction. -/
theorem cycleExecution_step (t : Nat) :
    sealMacroProtocol.step ringSix (cycleExecution t)
        (roundRobinSchedule t) =
      cycleExecution (t + 1) := by
  rcases modSix_cases t with ht | ht | ht | ht | ht | ht
  · have hn : (t + 1) % 6 = 1 := by omega
    have hs : roundRobinSchedule t = (0 : Fin 6) := by
      apply Fin.ext
      exact ht
    rw [show cycleExecution t = cycleC0 by simp [cycleExecution, ht], hs,
      show cycleExecution (t + 1) = cycleC1 by simp [cycleExecution, hn]]
    exact cycle_step_zero
  · have hn : (t + 1) % 6 = 2 := by omega
    have hs : roundRobinSchedule t = (1 : Fin 6) := by
      apply Fin.ext
      exact ht
    rw [show cycleExecution t = cycleC1 by simp [cycleExecution, ht], hs,
      show cycleExecution (t + 1) = cycleC2 by simp [cycleExecution, hn]]
    exact cycle_step_one
  · have hn : (t + 1) % 6 = 3 := by omega
    have hs : roundRobinSchedule t = (2 : Fin 6) := by
      apply Fin.ext
      exact ht
    rw [show cycleExecution t = cycleC2 by simp [cycleExecution, ht], hs,
      show cycleExecution (t + 1) = cycleC3 by simp [cycleExecution, hn]]
    exact cycle_step_two
  · have hn : (t + 1) % 6 = 4 := by omega
    have hs : roundRobinSchedule t = (3 : Fin 6) := by
      apply Fin.ext
      exact ht
    rw [show cycleExecution t = cycleC3 by simp [cycleExecution, ht], hs,
      show cycleExecution (t + 1) = cycleC4 by simp [cycleExecution, hn]]
    exact cycle_step_three
  · have hn : (t + 1) % 6 = 5 := by omega
    have hs : roundRobinSchedule t = (4 : Fin 6) := by
      apply Fin.ext
      exact ht
    rw [show cycleExecution t = cycleC4 by simp [cycleExecution, ht], hs,
      show cycleExecution (t + 1) = cycleC5 by simp [cycleExecution, hn]]
    exact cycle_step_four
  · have hn : (t + 1) % 6 = 0 := by omega
    have hs : roundRobinSchedule t = (5 : Fin 6) := by
      apply Fin.ext
      exact ht
    rw [show cycleExecution t = cycleC5 by simp [cycleExecution, ht], hs,
      show cycleExecution (t + 1) = cycleC0 by simp [cycleExecution, hn]]
    exact cycle_step_five

theorem cycleExecution_hasTwo (t : Nat) :
    MacroHasTwoLeaders (cycleExecution t) := by
  rcases modSix_cases t with ht | ht | ht | ht | ht | ht
  · simpa [cycleExecution, ht] using cycleC0_hasTwo
  · simpa [cycleExecution, ht] using cycleC1_hasTwo
  · simpa [cycleExecution, ht] using cycleC2_hasTwo
  · simpa [cycleExecution, ht] using cycleC3_hasTwo
  · simpa [cycleExecution, ht] using cycleC4_hasTwo
  · simpa [cycleExecution, ht] using cycleC5_hasTwo

theorem cycleExecution_not_isSafe (t : Nat) :
    ¬ PopulationProtocol.IsSafe
      sealMacroProtocol ringSix (cycleExecution t) id := by
  intro hsafe
  exact macroHasTwo_not_unique (cycleExecution_hasTwo t) hsafe.1

theorem cycleExecution_reachable (t : Nat) :
    PopulationProtocol.Reachable
      sealMacroProtocol ringSix cycleC0 (cycleExecution t) := by
  induction t with
  | zero =>
      rw [cycleExecution_initial]
      exact PopulationProtocol.Reachable.refl cycleC0
  | succ t ih =>
      exact PopulationProtocol.Reachable.step
        cycleC0 (cycleExecution t) (cycleExecution (t + 1)) ih
        ⟨roundRobinSchedule t, (cycleExecution_step t).symm⟩

/-- Complete nonconvergence certificate: a literal protocol execution, a
schedule selecting every edge infinitely often, and two leader outputs at
every time. -/
theorem exists_weakEdgeFair_twoLeader_execution :
    ∃ schedule : Nat → Fin 6,
      ∃ execution : Nat → SealMacroConfig 6,
        execution 0 = cycleC0 ∧
        WeakEdgeFair schedule ∧
        (∀ t, sealMacroProtocol.step ringSix (execution t) (schedule t) =
          execution (t + 1)) ∧
        (∀ t, MacroHasTwoLeaders (execution t)) ∧
        (∀ t, ¬ PopulationProtocol.IsSafe
          sealMacroProtocol ringSix (execution t) id) := by
  exact ⟨roundRobinSchedule, cycleExecution,
    cycleExecution_initial, roundRobinSchedule_fair,
    cycleExecution_step, cycleExecution_hasTwo, cycleExecution_not_isSafe⟩

/-! ## A cycle whose initial word is entirely sealed -/

/-- The macro-level sealed predicate. -/
def sealMacroSealed : SealMacroState → Bool
  | LS | FS => true
  | LU | FU => false

def MacroAllSealed (C : SealMacroConfig 6) : Prop :=
  ∀ i : Fin 6, sealMacroSealed (C i) = true

/-- Exact all-sealed starting word `LS, FS, FS, LS, FS, FS`. -/
def sealedCycleC0 : SealMacroConfig 6 := fun i =>
  match i.val with
  | 0 => LS
  | 1 => FS
  | 2 => FS
  | 3 => LS
  | 4 => FS
  | _ => FS

/-- Successive configurations under the permutation word
`0,3,1,2,4,5`. -/
def sealedCycleC1 : SealMacroConfig 6 :=
  sealMacroProtocol.step ringSix sealedCycleC0 0

def sealedCycleC2 : SealMacroConfig 6 :=
  sealMacroProtocol.step ringSix sealedCycleC1 3

def sealedCycleC3 : SealMacroConfig 6 :=
  sealMacroProtocol.step ringSix sealedCycleC2 1

def sealedCycleC4 : SealMacroConfig 6 :=
  sealMacroProtocol.step ringSix sealedCycleC3 2

def sealedCycleC5 : SealMacroConfig 6 :=
  sealMacroProtocol.step ringSix sealedCycleC4 4

def sealedCycleC6 : SealMacroConfig 6 :=
  sealMacroProtocol.step ringSix sealedCycleC5 5

theorem sealedCycle_step_zero :
    sealMacroProtocol.step ringSix sealedCycleC0 0 = sealedCycleC1 := by
  rfl

theorem sealedCycle_step_three :
    sealMacroProtocol.step ringSix sealedCycleC1 3 = sealedCycleC2 := by
  rfl

theorem sealedCycle_step_one :
    sealMacroProtocol.step ringSix sealedCycleC2 1 = sealedCycleC3 := by
  rfl

theorem sealedCycle_step_two :
    sealMacroProtocol.step ringSix sealedCycleC3 2 = sealedCycleC4 := by
  rfl

theorem sealedCycle_step_four :
    sealMacroProtocol.step ringSix sealedCycleC4 4 = sealedCycleC5 := by
  rfl

theorem sealedCycle_step_five :
    sealMacroProtocol.step ringSix sealedCycleC5 5 = sealedCycleC0 := by
  change sealedCycleC6 = sealedCycleC0
  funext i
  rcases finSix_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

def sealedCycleWord : List (Fin 6) := [0, 3, 1, 2, 4, 5]

theorem sealedCycleWord_length : sealedCycleWord.length = 6 := by
  rfl

theorem run_sealedCycleWord_eq :
    runSchedule sealMacroProtocol ringSix sealedCycleC0 sealedCycleWord =
      sealedCycleC0 := by
  change sealedCycleC6 = sealedCycleC0
  exact sealedCycle_step_five

theorem sealedCycleC0_allSealed : MacroAllSealed sealedCycleC0 := by
  intro i
  rcases finSix_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem finSix_zero_ne_three : (0 : Fin 6) ≠ (3 : Fin 6) := by
  decide

theorem sealedCycleC0_hasTwo : MacroHasTwoLeaders sealedCycleC0 := by
  exact ⟨0, 3, finSix_zero_ne_three, rfl, rfl⟩

theorem sealedCycleC1_hasTwo : MacroHasTwoLeaders sealedCycleC1 := by
  exact ⟨0, 3, finSix_zero_ne_three, rfl, rfl⟩

theorem sealedCycleC2_hasTwo : MacroHasTwoLeaders sealedCycleC2 := by
  exact ⟨0, 3, finSix_zero_ne_three, rfl, rfl⟩

theorem sealedCycleC3_hasTwo : MacroHasTwoLeaders sealedCycleC3 := by
  exact ⟨0, 3, finSix_zero_ne_three, rfl, rfl⟩

theorem sealedCycleC4_hasTwo : MacroHasTwoLeaders sealedCycleC4 := by
  exact ⟨0, 3, finSix_zero_ne_three, rfl, rfl⟩

theorem sealedCycleC5_hasTwo : MacroHasTwoLeaders sealedCycleC5 := by
  exact ⟨0, 3, finSix_zero_ne_three, rfl, rfl⟩

/-! ## Periodic repetition of the sealed-start permutation -/

def sealedPermutationSchedule (t : Nat) : Fin 6 :=
  match t % 6 with
  | 0 => 0
  | 1 => 3
  | 2 => 1
  | 3 => 2
  | 4 => 4
  | _ => 5

private theorem sealedPermutationSchedule_phase_zero (q : Nat) :
    sealedPermutationSchedule (6 * q + 0) = (0 : Fin 6) := by
  apply Fin.ext
  simp [sealedPermutationSchedule]

private theorem sealedPermutationSchedule_phase_one (q : Nat) :
    sealedPermutationSchedule (6 * q + 1) = (3 : Fin 6) := by
  apply Fin.ext
  have hm : (6 * q + 1) % 6 = 1 := by omega
  simp [sealedPermutationSchedule, hm]

private theorem sealedPermutationSchedule_phase_two (q : Nat) :
    sealedPermutationSchedule (6 * q + 2) = (1 : Fin 6) := by
  apply Fin.ext
  have hm : (6 * q + 2) % 6 = 2 := by omega
  simp [sealedPermutationSchedule, hm]

private theorem sealedPermutationSchedule_phase_three (q : Nat) :
    sealedPermutationSchedule (6 * q + 3) = (2 : Fin 6) := by
  apply Fin.ext
  have hm : (6 * q + 3) % 6 = 3 := by omega
  simp [sealedPermutationSchedule, hm]

private theorem sealedPermutationSchedule_phase_four (q : Nat) :
    sealedPermutationSchedule (6 * q + 4) = (4 : Fin 6) := by
  apply Fin.ext
  have hm : (6 * q + 4) % 6 = 4 := by omega
  simp [sealedPermutationSchedule, hm]

private theorem sealedPermutationSchedule_phase_five (q : Nat) :
    sealedPermutationSchedule (6 * q + 5) = (5 : Fin 6) := by
  apply Fin.ext
  have hm : (6 * q + 5) % 6 = 5 := by omega
  simp [sealedPermutationSchedule, hm]

theorem sealedPermutationSchedule_fair :
    WeakEdgeFair sealedPermutationSchedule := by
  intro e t
  rcases finSix_cases e with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨6 * t + 0, by omega,
      sealedPermutationSchedule_phase_zero t⟩
  · exact ⟨6 * t + 2, by omega,
      sealedPermutationSchedule_phase_two t⟩
  · exact ⟨6 * t + 3, by omega,
      sealedPermutationSchedule_phase_three t⟩
  · exact ⟨6 * t + 1, by omega,
      sealedPermutationSchedule_phase_one t⟩
  · exact ⟨6 * t + 4, by omega,
      sealedPermutationSchedule_phase_four t⟩
  · exact ⟨6 * t + 5, by omega,
      sealedPermutationSchedule_phase_five t⟩

def sealedCycleExecution (t : Nat) : SealMacroConfig 6 :=
  match t % 6 with
  | 0 => sealedCycleC0
  | 1 => sealedCycleC1
  | 2 => sealedCycleC2
  | 3 => sealedCycleC3
  | 4 => sealedCycleC4
  | _ => sealedCycleC5

theorem sealedCycleExecution_initial :
    sealedCycleExecution 0 = sealedCycleC0 := by
  rfl

theorem sealedCycleExecution_step (t : Nat) :
    sealMacroProtocol.step ringSix (sealedCycleExecution t)
        (sealedPermutationSchedule t) =
      sealedCycleExecution (t + 1) := by
  rcases modSix_cases t with ht | ht | ht | ht | ht | ht
  · have hn : (t + 1) % 6 = 1 := by omega
    have hs : sealedPermutationSchedule t = (0 : Fin 6) := by
      apply Fin.ext
      simp [sealedPermutationSchedule, ht]
    rw [show sealedCycleExecution t = sealedCycleC0 by
          simp [sealedCycleExecution, ht],
      hs,
      show sealedCycleExecution (t + 1) = sealedCycleC1 by
        simp [sealedCycleExecution, hn]]
    exact sealedCycle_step_zero
  · have hn : (t + 1) % 6 = 2 := by omega
    have hs : sealedPermutationSchedule t = (3 : Fin 6) := by
      apply Fin.ext
      simp [sealedPermutationSchedule, ht]
    rw [show sealedCycleExecution t = sealedCycleC1 by
          simp [sealedCycleExecution, ht],
      hs,
      show sealedCycleExecution (t + 1) = sealedCycleC2 by
        simp [sealedCycleExecution, hn]]
    exact sealedCycle_step_three
  · have hn : (t + 1) % 6 = 3 := by omega
    have hs : sealedPermutationSchedule t = (1 : Fin 6) := by
      apply Fin.ext
      simp [sealedPermutationSchedule, ht]
    rw [show sealedCycleExecution t = sealedCycleC2 by
          simp [sealedCycleExecution, ht],
      hs,
      show sealedCycleExecution (t + 1) = sealedCycleC3 by
        simp [sealedCycleExecution, hn]]
    exact sealedCycle_step_one
  · have hn : (t + 1) % 6 = 4 := by omega
    have hs : sealedPermutationSchedule t = (2 : Fin 6) := by
      apply Fin.ext
      simp [sealedPermutationSchedule, ht]
    rw [show sealedCycleExecution t = sealedCycleC3 by
          simp [sealedCycleExecution, ht],
      hs,
      show sealedCycleExecution (t + 1) = sealedCycleC4 by
        simp [sealedCycleExecution, hn]]
    exact sealedCycle_step_two
  · have hn : (t + 1) % 6 = 5 := by omega
    have hs : sealedPermutationSchedule t = (4 : Fin 6) := by
      apply Fin.ext
      simp [sealedPermutationSchedule, ht]
    rw [show sealedCycleExecution t = sealedCycleC4 by
          simp [sealedCycleExecution, ht],
      hs,
      show sealedCycleExecution (t + 1) = sealedCycleC5 by
        simp [sealedCycleExecution, hn]]
    exact sealedCycle_step_four
  · have hn : (t + 1) % 6 = 0 := by omega
    have hs : sealedPermutationSchedule t = (5 : Fin 6) := by
      apply Fin.ext
      simp [sealedPermutationSchedule, ht]
    rw [show sealedCycleExecution t = sealedCycleC5 by
          simp [sealedCycleExecution, ht],
      hs,
      show sealedCycleExecution (t + 1) = sealedCycleC0 by
        simp [sealedCycleExecution, hn]]
    exact sealedCycle_step_five

theorem sealedCycleExecution_hasTwo (t : Nat) :
    MacroHasTwoLeaders (sealedCycleExecution t) := by
  rcases modSix_cases t with ht | ht | ht | ht | ht | ht
  · simpa [sealedCycleExecution, ht] using sealedCycleC0_hasTwo
  · simpa [sealedCycleExecution, ht] using sealedCycleC1_hasTwo
  · simpa [sealedCycleExecution, ht] using sealedCycleC2_hasTwo
  · simpa [sealedCycleExecution, ht] using sealedCycleC3_hasTwo
  · simpa [sealedCycleExecution, ht] using sealedCycleC4_hasTwo
  · simpa [sealedCycleExecution, ht] using sealedCycleC5_hasTwo

theorem sealedCycleExecution_not_isSafe (t : Nat) :
    ¬ PopulationProtocol.IsSafe
      sealMacroProtocol ringSix (sealedCycleExecution t) id := by
  intro hsafe
  exact macroHasTwo_not_unique (sealedCycleExecution_hasTwo t) hsafe.1

theorem sealedCycleExecution_reachable (t : Nat) :
    PopulationProtocol.Reachable
      sealMacroProtocol ringSix sealedCycleC0 (sealedCycleExecution t) := by
  induction t with
  | zero =>
      rw [sealedCycleExecution_initial]
      exact PopulationProtocol.Reachable.refl sealedCycleC0
  | succ t ih =>
      exact PopulationProtocol.Reachable.step
        sealedCycleC0 (sealedCycleExecution t) (sealedCycleExecution (t + 1)) ih
        ⟨sealedPermutationSchedule t, (sealedCycleExecution_step t).symm⟩

/-- Stronger certificate with an exact all-sealed source configuration. -/
theorem exists_allSealed_weakEdgeFair_twoLeader_execution :
    ∃ schedule : Nat → Fin 6,
      ∃ execution : Nat → SealMacroConfig 6,
        execution 0 = sealedCycleC0 ∧
        MacroAllSealed (execution 0) ∧
        WeakEdgeFair schedule ∧
        (∀ t, sealMacroProtocol.step ringSix (execution t) (schedule t) =
          execution (t + 1)) ∧
        (∀ t, MacroHasTwoLeaders (execution t)) ∧
        (∀ t, ¬ PopulationProtocol.IsSafe
          sealMacroProtocol ringSix (execution t) id) := by
  refine ⟨sealedPermutationSchedule, sealedCycleExecution,
    sealedCycleExecution_initial, ?_, sealedPermutationSchedule_fair,
    sealedCycleExecution_step, sealedCycleExecution_hasTwo,
    sealedCycleExecution_not_isSafe⟩
  rw [sealedCycleExecution_initial]
  exact sealedCycleC0_allSealed

end SealSweepConcurrentCycleSol
