import Leader.Wu.Birth.SigMoveDisposalRepair

set_option autoImplicit false

namespace BirthDisposalParametricWait

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair BirthCheckCongestGuardRepair
  BirthCheckParametricWait BirthSigMoveDisposalRepair

variable {n psi : Nat}

/-! Positive physical budgets give an exact cap-independent core projection
of the actual disposal repair.  Its cap-sixteen whole-host certificates then
supply the WAIT/GEN/transport/CHECK producer for every cap at least sixteen
and all four two-bit words.  No absent-disposal premise is assumed. -/

/-- Core projection of the actual early-disposal full transition. -/
def disposalCoreTransition (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    AuthorizedBoundedAgentState psi kappa × AuthorizedBoundedAgentState psi kappa :=
  guardedCoreTransition hpsi kappa
    (prepareBoundedDisposal hpsi l) (prepareBoundedDisposal hpsi r)

attribute [local irreducible] guardedFullTransition disposalFullTransition

private theorem full_core_of_positive (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : 0 < l.stall.val) (hr : 0 < r.stall.val) :
    let q := disposalFullTransition hpsi kappa tau l r
    (q.1.core, q.2.core) = disposalCoreTransition hpsi kappa l.core r.core := by
  unfold disposalFullTransition disposalCoreTransition
  exact guardedFullTransition_core_of_positive hpsi kappa tau
    (prepareExpiringDisposal hpsi l) (prepareExpiringDisposal hpsi r) hl hr

private theorem full_budget (hpsi : psi > 0) (kappa tau remaining : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hcap : remaining ≤ tau)
    (hl : remaining + 1 ≤ l.stall.val) (hr : remaining + 1 ≤ r.stall.val) :
    let q := disposalFullTransition hpsi kappa tau l r
    remaining ≤ q.1.stall.val ∧ remaining ≤ q.2.stall.val := by
  unfold disposalFullTransition
  exact guardedFullTransition_budget hpsi kappa tau remaining
    (prepareExpiringDisposal hpsi l) (prepareExpiringDisposal hpsi r) hcap hl hr

private theorem localStep_core
    (ring : DirectedRing n) (hpsi : psi > 0) (kappa tau : Nat)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (hpos : ∀ i, 0 < (C i).stall.val) :
    coreConfig (localStep ring (disposalFullTransition hpsi kappa tau) C e) =
      localStep ring (disposalCoreTransition hpsi kappa) (coreConfig C) e := by
  have hq := full_core_of_positive hpsi kappa tau
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
      (localStep ring (disposalFullTransition hpsi kappa tau) C e i).stall.val := by
  have hq := full_budget hpsi kappa tau remaining
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
theorem run_disposal_core_of_budget
    (ring : DirectedRing n) (hpsi : psi > 0) (kappa tau : Nat)
    (C : Fin n → ExpiringAgentState psi kappa tau) (word : DetSchedule n)
    (hcap : word.length ≤ tau)
    (hcredit : ∀ i, word.length ≤ (C i).stall.val) :
    coreConfig (runLocalSchedule ring
      (disposalFullTransition hpsi kappa tau) C word) =
      runLocalSchedule ring (disposalCoreTransition hpsi kappa) (coreConfig C) word := by
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

open BirthFullHostRulerCounterexample

/-- The ordinary thirteen-edge source/transport word in the actual repair. -/
def disposalFamilyPrefix (tau : Nat) (a b : Bool) (t : Nat) :
    Fin 8 → ExpiringAgentState 2 2 tau :=
  runLocalSchedule ringEight (disposalFullTransition (by omega) 2 tau)
    (familyInitial tau a b) (equalSchedule.take t)

/-- The supplied fresh initial budgets discharge every projection premise.
All caps at least sixteen give the same full core at every prefix. -/
theorem disposal_family_core (tau : Nat) (htau : 16 ≤ tau)
    (a b : Bool) (t : Nat) (i : Fin 8) :
    (disposalFamilyPrefix tau a b t i).core =
      (disposalFamilyPrefix 16 a b t i).core := by
  have hword16 : (equalSchedule.take t).length ≤ 16 := by
    simp only [List.length_take, equalSchedule, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil]
    omega
  have hword : (equalSchedule.take t).length ≤ tau := Nat.le_trans hword16 htau
  have h := run_disposal_core_of_budget ringEight (by omega) 2 tau
    (familyInitial tau a b) (equalSchedule.take t) hword (fun _ => hword)
  have h16 := run_disposal_core_of_budget ringEight (by omega) 2 16
    (familyInitial 16 a b) (equalSchedule.take t) hword16 (fun _ => hword16)
  exact (congrFun h i).trans (congrFun h16 i).symm

/-- All four real source words remain live for every expiry cap at least
sixteen, from the explicit leaderless WAIT-true/count-zero/empty-path state.
This is the complete finite disposal repair, not its core projection. -/
theorem disposal_family_creates_unique_leader
    (tau : Nat) (htau : 16 ≤ tau) (a b : Bool) :
    (∀ i : Fin 8, (disposalFamilyPrefix tau a b 13 i).core.core.leader = true ↔ i = 2) ∧
      (disposalFamilyPrefix tau a b 13 2).core.core.label = 0 ∧
      (disposalFamilyPrefix tau a b 13 2).core.core.signal_B = 0 := by
  simp only [disposal_family_core tau htau]
  have hword : equalSchedule.take 13 = equalSchedule := by decide
  simpa only [disposalFamilyPrefix, hword] using disposal_accepts_all_two_bit_words a b

attribute [local semireducible] guardedFullTransition disposalFullTransition

private theorem get_ofFn {Q : Type} (C : Fin 8 → Q) :
    (Vector.ofFn C).get = C := by
  funext i
  simp [Vector.get]
  apply congrArg C
  apply Fin.ext
  rfl

private def cachedRun {Q : Type} (T : Q → Q → Q × Q) :
    DetSchedule 8 → Vector Q 8 → Vector Q 8
  | [], C => C
  | e :: rest, C => cachedRun T rest (Vector.ofFn (localStep ringEight T C.get e))

private theorem cachedRun_correct {Q : Type} (T : Q → Q → Q × Q)
    (C : Fin 8 → Q) (word : DetSchedule 8) :
    (cachedRun T word (Vector.ofFn C)).get = runLocalSchedule ringEight T C word := by
  induction word generalizing C with
  | nil => exact get_ofFn C
  | cons e rest ih =>
      simp only [cachedRun, get_ofFn, runLocalSchedule]
      exact ih _

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- Actual WAIT creates both components when its count reaches two; the
whole same-generation word then arrives at the next group with ready states
and true physical crossing permission on its zero component. -/
theorem disposal_reference_generated_and_arrived (a b : Bool) :
    (disposalFamilyPrefix 16 a b 7 0).core.core.path = .bot ∧
      (disposalFamilyPrefix 16 a b 7 1).core.core.path = .bot ∧
      (disposalFamilyPrefix 16 a b 7 1).core.core.count = 1 ∧
      (disposalFamilyPrefix 16 a b 8 1).core.core.count = 2 ∧
      (disposalFamilyPrefix 16 a b 8 0).core.core.path = .some 0 (if a then 1 else 0) ∧
      (disposalFamilyPrefix 16 a b 8 1).core.core.path = .some 1 (if b then 1 else 0) ∧
      (disposalFamilyPrefix 16 a b 12 2).core.core.path = .some 0 (if a then 1 else 0) ∧
      (disposalFamilyPrefix 16 a b 12 2).core.core.state = .CHECK_ready ∧
      (disposalFamilyPrefix 16 a b 12 2).core.path0Crossed = true ∧
      (disposalFamilyPrefix 16 a b 12 3).core.core.path = .some 1 (if b then 1 else 0) ∧
      (disposalFamilyPrefix 16 a b 12 3).core.core.state = .CHECK_ready := by
  cases a <;> cases b <;>
    unfold disposalFamilyPrefix <;>
    simp only [← cachedRun_correct] <;> decide

/-- The real producer persists throughout the physical parameter family;
no abstract source-history or successful-CHECK condition is an input. -/
theorem disposal_family_generated_and_arrived
    (tau : Nat) (htau : 16 ≤ tau) (a b : Bool) :
    (disposalFamilyPrefix tau a b 7 0).core.core.path = .bot ∧
      (disposalFamilyPrefix tau a b 7 1).core.core.path = .bot ∧
      (disposalFamilyPrefix tau a b 7 1).core.core.count = 1 ∧
      (disposalFamilyPrefix tau a b 8 1).core.core.count = 2 ∧
      (disposalFamilyPrefix tau a b 8 0).core.core.path = .some 0 (if a then 1 else 0) ∧
      (disposalFamilyPrefix tau a b 8 1).core.core.path = .some 1 (if b then 1 else 0) ∧
      (disposalFamilyPrefix tau a b 12 2).core.core.path = .some 0 (if a then 1 else 0) ∧
      (disposalFamilyPrefix tau a b 12 2).core.core.state = .CHECK_ready ∧
      (disposalFamilyPrefix tau a b 12 2).core.path0Crossed = true ∧
      (disposalFamilyPrefix tau a b 12 3).core.core.path = .some 1 (if b then 1 else 0) ∧
      (disposalFamilyPrefix tau a b 12 3).core.core.state = .CHECK_ready := by
  simp only [disposal_family_core tau htau]
  exact disposal_reference_generated_and_arrived a b

end BirthDisposalParametricWait

#print axioms BirthDisposalParametricWait.run_disposal_core_of_budget
#print axioms BirthDisposalParametricWait.disposal_family_core
#print axioms BirthDisposalParametricWait.disposal_family_creates_unique_leader
#print axioms BirthDisposalParametricWait.disposal_family_generated_and_arrived
