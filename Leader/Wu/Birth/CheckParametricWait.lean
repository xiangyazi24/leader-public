import Leader.Wu.Birth.CheckCongestGuardRepair

set_option autoImplicit false

namespace BirthCheckParametricWait

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLPathStallComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepPreCheckResetRepair
  BirthCheckCongestGuardRepair

variable {n psi kappa tau : Nat}

/-! This module removes the fixed expiry-cap value from the complete physical
WAIT/GEN/transport/CHECK witness.  Positive endpoint budgets make expiry frame
the counted core; each interaction spends at most one budget unit.  The
resulting finite-word projection is proved for the actual guarded full host.
Its concrete application below supplies the budget and the initial clean
state, rather than assuming a successful comparison or a provenance flag. -/

/-- Forget only the expiry counter, retaining every executable control field. -/
def coreConfig (C : Fin n → ExpiringAgentState psi kappa tau) :
    Fin n → AuthorizedBoundedAgentState psi kappa := fun i => (C i).core

/-- The existing leader-signal postprocessor projected to its bounded core. -/
def clearLeaderSignalCore (s : AuthorizedBoundedAgentState psi kappa) :
    AuthorizedBoundedAgentState psi kappa :=
  (clearExpiringLeaderSignal (⟨s, 0⟩ : ExpiringAgentState psi kappa 0)).core

private theorem clearLeaderSignal_core
    (s : ExpiringAgentState psi kappa tau) :
    (clearExpiringLeaderSignal s).core = clearLeaderSignalCore s.core := by
  unfold clearLeaderSignalCore clearExpiringLeaderSignal
  split <;> rfl

/-- Core projection of the guarded full host before expiry can remove a
carrier.  This is an auxiliary projection, not a replacement transition. -/
def guardedCoreTransition (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa :=
  let q := guardedBoundedTransition hpsi kappa l r
  if l.core.leader = false ∧ r.core.leader = false then
    (clearLeaderSignalCore q.1, clearLeaderSignalCore q.2)
  else q

attribute [local irreducible] guardedBoundedTransition

/-- An endpoint with positive expiry credit retains the entire base output
core, regardless of whether that interaction refreshes or spends credit. -/
theorem expiry_core_of_positive
    (old out : ExpiringAgentState psi kappa tau)
    (hpos : 0 < old.stall.val) :
    (deletionPriorityExpireOne tau old out).core = out.core := by
  unfold deletionPriorityExpireOne pathExpireOne
  split
  · rfl
  · split
    · rfl
    · split
      · omega
      · rfl

/-- Every endpoint interaction spends at most one unit; either refresh
branch supplies the common remaining-word bound from the cap. -/
theorem expiry_budget (remaining : Nat)
    (old out : ExpiringAgentState psi kappa tau)
    (hcap : remaining ≤ tau)
    (hcredit : remaining + 1 ≤ old.stall.val) :
    remaining ≤ (deletionPriorityExpireOne tau old out).stall.val := by
  unfold deletionPriorityExpireOne pathExpireOne
  split
  · exact hcap
  · split
    · exact hcap
    · split
      · exact hcap
      · simp only [decStall]
        omega

/-- With positive input credit, the real full transition projects exactly to
the same bounded core transition for every expiry-cap value. -/
theorem guardedFullTransition_core_of_positive
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : 0 < l.stall.val) (hr : 0 < r.stall.val) :
    let q := guardedFullTransition hpsi kappa tau l r
    (q.1.core, q.2.core) = guardedCoreTransition hpsi kappa l.core r.core := by
  let q := guardedBoundedTransition hpsi kappa l.core r.core
  let lOut : ExpiringAgentState psi kappa tau := ⟨q.1, l.stall⟩
  let rOut : ExpiringAgentState psi kappa tau := ⟨q.2, r.stall⟩
  have hlCore := expiry_core_of_positive l lOut hl
  have hrCore := expiry_core_of_positive r rOut hr
  unfold guardedFullTransition guardedPathStallTransition
    initializeFollowerPairBirthSignals guardedCoreTransition
  dsimp only
  split
  · simp only [clearLeaderSignal_core]
    change (clearLeaderSignalCore (deletionPriorityExpireOne tau l lOut).core,
      clearLeaderSignalCore (deletionPriorityExpireOne tau r rOut).core) = _
    rw [hlCore, hrCore]
  · change ((deletionPriorityExpireOne tau l lOut).core,
      (deletionPriorityExpireOne tau r rOut).core) = _
    rw [hlCore, hrCore]

/-- The final birth-signal wrapper preserves the endpoint budget guarantee. -/
theorem guardedFullTransition_budget
    (hpsi : psi > 0) (kappa tau remaining : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hcap : remaining ≤ tau)
    (hl : remaining + 1 ≤ l.stall.val)
    (hr : remaining + 1 ≤ r.stall.val) :
    let q := guardedFullTransition hpsi kappa tau l r
    remaining ≤ q.1.stall.val ∧ remaining ≤ q.2.stall.val := by
  let q := guardedBoundedTransition hpsi kappa l.core r.core
  let lOut : ExpiringAgentState psi kappa tau := ⟨q.1, l.stall⟩
  let rOut : ExpiringAgentState psi kappa tau := ⟨q.2, r.stall⟩
  have hlBudget := expiry_budget remaining l lOut hcap hl
  have hrBudget := expiry_budget remaining r rOut hcap hr
  unfold guardedFullTransition guardedPathStallTransition
    initializeFollowerPairBirthSignals
  dsimp only
  split
  · simp only [clearExpiringLeaderSignal_stall]
    exact ⟨hlBudget, hrBudget⟩
  · exact ⟨hlBudget, hrBudget⟩

private theorem localStep_core
    (ring : DirectedRing n) (hpsi : psi > 0) (kappa tau : Nat)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (hpos : ∀ i, 0 < (C i).stall.val) :
    coreConfig (localStep ring (guardedFullTransition hpsi kappa tau) C e) =
      localStep ring (guardedCoreTransition hpsi kappa) (coreConfig C) e := by
  have hq := guardedFullTransition_core_of_positive hpsi kappa tau
    (C e) (C (ring.rightNeighbor e)) (hpos e) (hpos (ring.rightNeighbor e))
  have hleft := congrArg Prod.fst hq
  have hright := congrArg Prod.snd hq
  funext i
  unfold coreConfig localStep
  dsimp only
  split
  · exact hleft
  · split
    · exact hright
    · rfl

private theorem localStep_budget
    (ring : DirectedRing n) (hpsi : psi > 0) (kappa tau remaining : Nat)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (hcap : remaining ≤ tau)
    (hcredit : ∀ i, remaining + 1 ≤ (C i).stall.val) :
    ∀ i, remaining ≤
      (localStep ring (guardedFullTransition hpsi kappa tau) C e i).stall.val := by
  have hq := guardedFullTransition_budget hpsi kappa tau remaining
    (C e) (C (ring.rightNeighbor e)) hcap
    (hcredit e) (hcredit (ring.rightNeighbor e))
  intro i
  unfold localStep
  split
  · exact hq.1
  · split
    · exact hq.2
    · have := hcredit i
      omega

/-- A concrete word shorter than the supplied physical expiry budgets has
an exact cap-independent core execution.  Both premises are discharged by
the fresh-budget initial family used below. -/
theorem run_core_of_budget
    (ring : DirectedRing n) (hpsi : psi > 0) (kappa tau : Nat)
    (C : Fin n → ExpiringAgentState psi kappa tau) (word : DetSchedule n)
    (hcap : word.length ≤ tau)
    (hcredit : ∀ i, word.length ≤ (C i).stall.val) :
    coreConfig (runLocalSchedule ring
      (guardedFullTransition hpsi kappa tau) C word) =
      runLocalSchedule ring (guardedCoreTransition hpsi kappa) (coreConfig C) word := by
  induction word generalizing C with
  | nil => rfl
  | cons e rest ih =>
      have hcap' : rest.length ≤ tau := by
        simp only [List.length_cons] at hcap
        omega
      have hcredit' := localStep_budget ring hpsi kappa tau rest.length C e
        hcap' (by simpa using hcredit)
      have hpos : ∀ i, 0 < (C i).stall.val := by
        intro i
        have := hcredit i
        simp only [List.length_cons] at this
        omega
      rw [runLocalSchedule, ih _ hcap' hcredit']
      rw [localStep_core ring hpsi kappa tau C e hpos]
      rfl

attribute [local semireducible] guardedBoundedTransition

/-! ## All two-bit words and an unbounded family of expiry caps -/

/-- Every group initially has the same arbitrary two-bit word.  The complete
core is otherwise the earlier clean leaderless WAIT-true initial state. -/
def familyCore (a b : Bool) (i : Fin 8) : AuthorizedBoundedAgentState 2 2 :=
  let s := equalInitial i
  { s.core with core := { s.core.core with
    bit := if i.val % 2 = 0 then a else b } }

/-- Fresh physical timer values supply the finite-word budget explicitly;
all comparison paths, permissions, and WAIT counts still begin empty/zero. -/
def familyInitial (tau : Nat) (a b : Bool) (i : Fin 8) :
    ExpiringAgentState 2 2 tau :=
  ⟨familyCore a b i, freshStall tau⟩

theorem familyInitial_clean (tau : Nat) (a b : Bool) :
    ∀ i : Fin 8,
      (familyInitial tau a b i).core.core.leader = false ∧
      (familyInitial tau a b i).core.core.wait = true ∧
      (familyInitial tau a b i).core.core.count = 0 ∧
      (familyInitial tau a b i).core.core.path = .bot ∧
      (familyInitial tau a b i).core.path0Crossed = false ∧
      (familyInitial tau a b i).core.core.state = .none ∧
      (familyInitial tau a b i).stall.val = tau := by
  intro i
  have h := equalInitial_clean i
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    h.2.2.2.2.1, h.2.2.2.2.2, rfl⟩

def familyCorePrefix (a b : Bool) (t : Nat) :
    Fin 8 → AuthorizedBoundedAgentState 2 2 :=
  runLocalSchedule BirthFullHostRulerCounterexample.ringEight
    (guardedCoreTransition (by omega) 2) (familyCore a b)
    (equalSchedule.take t)

def familyPrefix (tau : Nat) (a b : Bool) (t : Nat) :
    Fin 8 → ExpiringAgentState 2 2 tau :=
  runLocalSchedule BirthFullHostRulerCounterexample.ringEight
    (guardedFullTransition (by omega) 2 tau) (familyInitial tau a b)
    (equalSchedule.take t)

/-- Every prefix has length at most thirteen, so every tau at least sixteen
admits the same exact core trajectory from the supplied fresh-budget state. -/
theorem familyPrefix_core (tau : Nat) (htau : 16 ≤ tau)
    (a b : Bool) (t : Nat) (i : Fin 8) :
    (familyPrefix tau a b t i).core = familyCorePrefix a b t i := by
  have hword : (equalSchedule.take t).length ≤ tau := by
    simp only [List.length_take, equalSchedule, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil]
    omega
  have hcredit : ∀ j : Fin 8, (equalSchedule.take t).length ≤
      (familyInitial tau a b j).stall.val := fun _ => hword
  have h := run_core_of_budget BirthFullHostRulerCounterexample.ringEight
    (by omega) 2 tau (familyInitial tau a b) (equalSchedule.take t) hword hcredit
  exact congrFun h i

private theorem core_get_ofFn (C : Fin 8 → AuthorizedBoundedAgentState 2 2) :
    (Vector.ofFn C).get = C := by
  funext i
  simp [Vector.get]
  apply congrArg C
  apply Fin.ext
  rfl

private def cachedCoreRun : DetSchedule 8 →
    Vector (AuthorizedBoundedAgentState 2 2) 8 →
    Vector (AuthorizedBoundedAgentState 2 2) 8
  | [], C => C
  | e :: rest, C => cachedCoreRun rest (Vector.ofFn
      (localStep BirthFullHostRulerCounterexample.ringEight
        (guardedCoreTransition (by omega) 2) C.get e))

private theorem cachedCoreRun_correct
    (C : Fin 8 → AuthorizedBoundedAgentState 2 2) (word : DetSchedule 8) :
    (cachedCoreRun word (Vector.ofFn C)).get =
      runLocalSchedule BirthFullHostRulerCounterexample.ringEight
        (guardedCoreTransition (by omega) 2) C word := by
  induction word generalizing C with
  | nil => exact core_get_ofFn C
  | cons e rest ih =>
      simp only [cachedCoreRun, core_get_ofFn, runLocalSchedule]
      exact ih _

/-- For each of the four source words, ordinary WAIT reaches count two and
GEN creates both components together, with their actual source bits. -/
theorem familyCore_generated (a b : Bool) :
    (∀ t : Fin 8, ∀ i : Fin 8, (familyCorePrefix a b t.val i).core.path = .bot) ∧
      (familyCorePrefix a b 7 1).core.count = 1 ∧
      (familyCorePrefix a b 8 1).core.count = 2 ∧
      (familyCorePrefix a b 8 0).core.path = .some 0 (if a then 1 else 0) ∧
      (familyCorePrefix a b 8 1).core.path = .some 1 (if b then 1 else 0) ∧
      (familyCorePrefix a b 8 0).core.state = .depart ∧
      (familyCorePrefix a b 8 1).core.state = .depart ∧
      (familyCorePrefix a b 8 0).path0Crossed = false ∧
      (familyCorePrefix a b 8 1).path0Crossed = false := by
  cases a <;> cases b <;>
    unfold familyCorePrefix <;>
    simp only [← cachedCoreRun_correct] <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The whole same-generation word reaches the next group; its zero
component receives permission from the real terminal-to-zero crossing. -/
theorem familyCore_arrived (a b : Bool) :
    (familyCorePrefix a b 9 2).core.path = .some 1 (if b then 1 else 0) ∧
      (familyCorePrefix a b 10 1).core.path = .some 0 (if a then 1 else 0) ∧
      (familyCorePrefix a b 11 3).core.path = .some 1 (if b then 1 else 0) ∧
      (familyCorePrefix a b 12 2).core.path = .some 0 (if a then 1 else 0) ∧
      (familyCorePrefix a b 12 2).core.state = .CHECK_ready ∧
      (familyCorePrefix a b 12 2).path0Crossed = true ∧
      (familyCorePrefix a b 12 3).core.path = .some 1 (if b then 1 else 0) ∧
      (familyCorePrefix a b 12 3).core.state = .CHECK_ready := by
  cases a <;> cases b <;>
    unfold familyCorePrefix <;>
    simp only [← cachedCoreRun_correct] <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The guarded CHECK and the complete following host stages accept every
matching two-bit word, yielding one actual zero-signal leader. -/
theorem familyCore_birth (a b : Bool) :
    (∀ i : Fin 8, (familyCorePrefix a b 13 i).core.leader = true ↔ i = 2) ∧
      (familyCorePrefix a b 13 2).core.label = 0 ∧
      (familyCorePrefix a b 13 2).core.signal_B = 0 := by
  cases a <;> cases b <;>
    unfold familyCorePrefix <;>
    simp only [← cachedCoreRun_correct] <;> decide

/-- An infinite physical parameter family, not a fixed-cap replay: for
every tau at least sixteen and every two-bit word, the thirteen-step ordinary
WAIT/GEN/transport/CHECK word creates exactly one leader from the explicit
clean leaderless state.  No global convergence claim is made. -/
theorem family_creates_unique_leader (tau : Nat) (htau : 16 ≤ tau)
    (a b : Bool) :
    equalSchedule.length = 13 ∧
      (∀ i : Fin 8, (familyPrefix tau a b 13 i).core.core.leader = true ↔ i = 2) ∧
      (familyPrefix tau a b 13 2).core.core.label = 0 ∧
      (familyPrefix tau a b 13 2).core.core.signal_B = 0 := by
  simp only [familyPrefix_core tau htau]
  exact ⟨by decide, familyCore_birth a b⟩

/-- The parameter-family execution has a real same-generation producer and
arrived CHECK-ready pair.  These statements concern the actual full host,
with initial WAIT true, count zero, empty paths, and false permissions. -/
theorem family_generated_and_arrived (tau : Nat) (htau : 16 ≤ tau)
    (a b : Bool) :
    (∀ t : Fin 8, ∀ i : Fin 8, (familyPrefix tau a b t.val i).core.core.path = .bot) ∧
      (familyPrefix tau a b 8 1).core.core.count = 2 ∧
      (familyPrefix tau a b 8 0).core.core.path = .some 0 (if a then 1 else 0) ∧
      (familyPrefix tau a b 8 1).core.core.path = .some 1 (if b then 1 else 0) ∧
      (familyPrefix tau a b 12 2).core.core.path = .some 0 (if a then 1 else 0) ∧
      (familyPrefix tau a b 12 2).core.core.state = .CHECK_ready ∧
      (familyPrefix tau a b 12 2).core.path0Crossed = true ∧
      (familyPrefix tau a b 12 3).core.core.path = .some 1 (if b then 1 else 0) ∧
      (familyPrefix tau a b 12 3).core.core.state = .CHECK_ready := by
  simp only [familyPrefix_core tau htau]
  have hg := familyCore_generated a b
  have ha := familyCore_arrived a b
  exact ⟨hg.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1,
    ha.2.2.2.1, ha.2.2.2.2.1, ha.2.2.2.2.2.1,
    ha.2.2.2.2.2.2.1, ha.2.2.2.2.2.2.2⟩

end BirthCheckParametricWait

#print axioms BirthCheckParametricWait.run_core_of_budget
#print axioms BirthCheckParametricWait.familyInitial_clean
#print axioms BirthCheckParametricWait.familyPrefix_core
#print axioms BirthCheckParametricWait.family_generated_and_arrived
#print axioms BirthCheckParametricWait.family_creates_unique_leader
