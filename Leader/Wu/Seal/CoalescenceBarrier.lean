import Leader.Wu.Seal.MixedRankDriftObstruction

/-!
# Exact iid leader-drop hazard and the first coalescence barrier

On `SealSweepPositiveDescendant`, the preceding module reduces semantic
safety exactly to `sealSweepLeaderCount = 1`.  This file computes the complete
one-step transition of that count.  A leader is removed precisely when the
responder is a closed leader and the initiator is either a closed leader or an
open follower.  Consequently the conditional one-step iid drop probability
is the number of such directed edges divided by the population size.

This exact drift numerator can vanish in a nonsafe positive descendant.  The
alternating all-open midpoint of the exact even family has arbitrarily large
population, at least two leaders, and no currently enabled leader-removal
edge.  Thus a polynomial coalescence proof cannot use a positive one-step
drift bound for leader count alone.  The first missing probabilistic statement
has to be a multi-step exposure bound: from every nonsafe positive descendant,
many scheduler words must create and then select a removal edge.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepIidCoalescenceBarrierSol

open PPLL PPLLResearchFormulation
open PPLLTraceConvergence
open PPLLStaticDoubleCoverNoGo
open PPartialDynamicSweepLockSol
open PPartialSealSweepOverlaySol
open PPartialSealSweepPositiveLandingSol
open PPartialSealSweepUniformSchedulerSol
open PPartialSealSweepMixedNormalizerSol
open PPartialSealSweepIidDriftObstructionSol
open PPartialSealSweepConcurrencyNoGoSol
open PPartialSealSweepConcurrentCounterfamilySol
open SealSweepConcurrentCycleSol
open SealSweepConcurrentCycleSol.SealMacroState
open SealSweepConcurrentCounterfamilySol

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## Exact leader-support transition -/

/-- Boolean test for the two and only two leader-removal pairs:
closed-leader/closed-leader and open-follower/closed-leader. -/
def sealSweepKillPair
    (l r : SealSweepState psi kappa tau) : Bool :=
  sweepLockLeader r && r.2 &&
    ((sweepLockLeader l && l.2) ||
      (!sweepLockLeader l && !l.2))

theorem sealSweepKillPair_eq_true_iff
    (l r : SealSweepState psi kappa tau) :
    sealSweepKillPair l r = true ↔
      sweepLockLeader r = true ∧ r.2 = true ∧
        ((sweepLockLeader l = true ∧ l.2 = true) ∨
          (sweepLockLeader l = false ∧ l.2 = false)) := by
  simp [sealSweepKillPair, Bool.or_eq_true, and_assoc]

/-- Exact responder support equation for the five-case overlay. -/
theorem sealSweep_pair_rightLeader_eq
    (l r : SealSweepState psi kappa tau) :
    sweepLockLeader (P_partialSealSweep l r).2 =
      (!sealSweepKillPair l r && sweepLockLeader r) := by
  cases hl : sweepLockLeader l <;>
    cases hlc : l.2 <;>
    cases hr : sweepLockLeader r <;>
    cases hrc : r.2
  all_goals
    simp only [sweepLockLeader] at hl hr
    simp [sealSweepKillPair, P_partialSealSweep,
      sweepLockLeader, hl, hlc, hr, hrc]

/-- Whether the directed edge currently removes its responder leader. -/
def sealSweepKillEdge
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) (e : Fin n) : Bool :=
  sealSweepKillPair (C e) (C (ring.rightNeighbor e))

/-- Every site other than the responder keeps its leader bit. -/
theorem sealSweep_localStep_leader_eq_of_ne_right
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) (e i : Fin n)
    (hi : i ≠ ring.rightNeighbor e) :
    sweepLockLeader (localStep ring P_partialSealSweep C e i) =
      sweepLockLeader (C i) := by
  by_cases hie : i = e
  · subst i
    simpa [localStep] using
      sealSweep_pair_leftLeader_eq
        (C e) (C (ring.rightNeighbor e))
  · simp [localStep, hie, hi]

/-- On a non-self ring, the responder leader bit is cleared exactly when the
selected edge passes `sealSweepKillEdge`. -/
theorem sealSweep_localStep_rightLeader_eq
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau) (e : Fin n) :
    sweepLockLeader
        (localStep ring P_partialSealSweep C e
          (ring.rightNeighbor e)) =
      (!sealSweepKillEdge ring C e &&
        sweepLockLeader (C (ring.rightNeighbor e))) := by
  have hne : ring.rightNeighbor e ≠ e :=
    rightNeighbor_ne_self_of_one_lt ring hn e
  simpa [localStep, sealSweepKillEdge, hne] using
    sealSweep_pair_rightLeader_eq
      (C e) (C (ring.rightNeighbor e))

private def finiteCoordSum {m : Nat} (f : Fin m → Nat) : Nat :=
  (List.ofFn f).sum

private theorem finiteCoordSum_succ {m : Nat}
    (f : Fin (m + 1) → Nat) :
    finiteCoordSum f = f 0 + finiteCoordSum (fun i : Fin m => f i.succ) := by
  unfold finiteCoordSum
  rw [List.ofFn_succ, List.sum_cons]

private theorem finiteCoordSum_zero (m : Nat) :
    finiteCoordSum (fun _i : Fin m => 0) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [finiteCoordSum_succ]
      simpa using ih

private theorem finiteCoordSum_single_change {m : Nat}
    (before after : Fin m → Nat) (victim : Fin m)
    (hother : ∀ i : Fin m, i ≠ victim → after i = before i) :
    finiteCoordSum after + before victim =
      finiteCoordSum before + after victim := by
  induction m with
  | zero => exact Fin.elim0 victim
  | succ m ih =>
      rw [finiteCoordSum_succ, finiteCoordSum_succ]
      cases victim using Fin.cases with
      | zero =>
          have htail :
              (fun i : Fin m => after i.succ) =
                fun i : Fin m => before i.succ := by
            funext i
            exact hother i.succ (Fin.succ_ne_zero i)
          rw [htail]
          omega
      | succ victim =>
          have hhead : after 0 = before 0 :=
            hother 0 (fun h => Fin.succ_ne_zero victim h.symm)
          have htail := ih
            (fun i : Fin m => before i.succ)
            (fun i : Fin m => after i.succ)
            victim
            (fun i hi => hother i.succ
              (fun h => hi (Fin.succ_inj.mp h)))
          rw [hhead]
          omega

/-- Exact additive transition law.  Every interaction removes either zero or
one leader, and the Boolean indicator is exactly `sealSweepKillEdge`. -/
theorem sealSweepLeaderCount_localStep_exact
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau) (e : Fin n) :
    sealSweepLeaderCount
        (localStep ring P_partialSealSweep C e) +
        (if sealSweepKillEdge ring C e then 1 else 0) =
      sealSweepLeaderCount C := by
  let j := ring.rightNeighbor e
  let D := localStep ring P_partialSealSweep C e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  have hotherLeader : ∀ i : Fin n, i ≠ j →
      sweepLockLeader (D i) = sweepLockLeader (C i) := by
    intro i hi
    exact sealSweep_localStep_leader_eq_of_ne_right ring C e i hi
  cases hk : sealSweepKillEdge ring C e
  · have hall : ∀ i : Fin n,
        sweepLockLeader (D i) = sweepLockLeader (C i) := by
      intro i
      by_cases hij : i = j
      · subst i
        simpa [D, j, hk] using
          sealSweep_localStep_rightLeader_eq ring hn C e
      · exact hotherLeader i hij
    have hcount : sealSweepLeaderCount D = sealSweepLeaderCount C := by
      unfold sealSweepLeaderCount
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext i
      rw [hall i]
    simpa [D, hk] using hcount
  · have hjBefore : sweepLockLeader (C j) = true := by
      cases hr : sweepLockLeader (C j)
      · simp [sealSweepKillEdge, sealSweepKillPair, j, hr] at hk
      · rfl
    have hjAfter : sweepLockLeader (D j) = false := by
      simpa [D, j, hk] using
        sealSweep_localStep_rightLeader_eq ring hn C e
    have hchange := finiteCoordSum_single_change
      (fun i : Fin n => if sweepLockLeader (C i) then 1 else 0)
      (fun i : Fin n => if sweepLockLeader (D i) then 1 else 0)
      j (by
        intro i hi
        rw [hotherLeader i hi])
    change sealSweepLeaderCount D + 1 = sealSweepLeaderCount C
    change finiteCoordSum
        (fun i : Fin n => if sweepLockLeader (D i) then 1 else 0) + 1 =
      finiteCoordSum
        (fun i : Fin n => if sweepLockLeader (C i) then 1 else 0)
    simpa [hjBefore, hjAfter] using hchange

/-- Strict one-step coalescence is equivalent to selecting a kill edge. -/
theorem sealSweepLeaderCount_localStep_lt_iff
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau) (e : Fin n) :
    sealSweepLeaderCount (localStep ring P_partialSealSweep C e) <
        sealSweepLeaderCount C ↔
      sealSweepKillEdge ring C e = true := by
  have h := sealSweepLeaderCount_localStep_exact ring hn C e
  cases hk : sealSweepKillEdge ring C e <;>
    simp [hk] at h ⊢ <;> omega

/-! ## A four-step adjacent-gap collision gadget -/

/-- A local `D,B,D,B` pattern supplies a four-interaction leader collision:
close both open pairs, relaunch the middle `A,C` pair, then let the new probe
hit the right closed leader.  This is the basic multi-step exposure mechanism
that a global iid argument would have to count across all current gaps. -/
theorem sealSweep_fourStep_openAlternatingQuad_drop
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau)
    (x y z w : Fin n)
    (hxy : ring.rightNeighbor x = y)
    (hyz : ring.rightNeighbor y = z)
    (hzw : ring.rightNeighbor z = w)
    (hxyNe : x ≠ y) (hxzNe : x ≠ z) (hxwNe : x ≠ w)
    (hyzNe : y ≠ z) (hywNe : y ≠ w) (hzwNe : z ≠ w)
    (hxLeader : sweepLockLeader (C x) = false)
    (hxOpen : (C x).2 = false)
    (hyLeader : sweepLockLeader (C y) = true)
    (hyOpen : (C y).2 = false)
    (hzLeader : sweepLockLeader (C z) = false)
    (hzOpen : (C z).2 = false)
    (hwLeader : sweepLockLeader (C w) = true)
    (hwOpen : (C w).2 = false) :
    sealSweepLeaderCount
        (runSchedule (P_partialSealSweepProtocol psi kappa tau) ring C
          [x, z, y, z]) + 1 =
      sealSweepLeaderCount C := by
  let C1 := localStep ring P_partialSealSweep C x
  let C2 := localStep ring P_partialSealSweep C1 z
  let C3 := localStep ring P_partialSealSweep C2 y
  let C4 := localStep ring P_partialSealSweep C3 z
  have hyxNe : y ≠ x := Ne.symm hxyNe
  have hzxNe : z ≠ x := Ne.symm hxzNe
  have hwxNe : w ≠ x := Ne.symm hxwNe
  have hzyNe : z ≠ y := Ne.symm hyzNe
  have hwyNe : w ≠ y := Ne.symm hywNe
  have hwzNe : w ≠ z := Ne.symm hzwNe
  have hpair1 : P_partialSealSweep (C x) (C y) =
      (((C x).1, true), ((C y).1, true)) :=
    P_partialSealSweep_return (C x) (C y)
      hxLeader hxOpen hyLeader hyOpen
  have hC1y : C1 y = ((C y).1, true) := by
    simp [C1, localStep, hxy, hyxNe, hpair1]
  have hC1z : C1 z = C z := by
    simp [C1, localStep, hxy, hzxNe, hzyNe]
  have hC1w : C1 w = C w := by
    simp [C1, localStep, hxy, hwxNe, hwyNe]
  have hC1yLeader : sweepLockLeader (C1 y) = true := by
    rw [hC1y]
    simpa [sweepLockLeader] using hyLeader
  have hC1yClosed : (C1 y).2 = true := by
    rw [hC1y]
  have hC1zLeader : sweepLockLeader (C1 z) = false := by
    rw [hC1z]
    exact hzLeader
  have hC1zOpen : (C1 z).2 = false := by
    rw [hC1z]
    exact hzOpen
  have hC1wLeader : sweepLockLeader (C1 w) = true := by
    rw [hC1w]
    exact hwLeader
  have hC1wOpen : (C1 w).2 = false := by
    rw [hC1w]
    exact hwOpen
  have hpair2 : P_partialSealSweep (C1 z) (C1 w) =
      (((C1 z).1, true), ((C1 w).1, true)) :=
    P_partialSealSweep_return (C1 z) (C1 w)
      hC1zLeader hC1zOpen hC1wLeader hC1wOpen
  have hC2y : C2 y = C1 y := by
    simp [C2, localStep, hzw, hyzNe, hywNe]
  have hC2z : C2 z = ((C1 z).1, true) := by
    simp [C2, localStep, hzw, hpair2]
  have hC2w : C2 w = ((C1 w).1, true) := by
    simp [C2, localStep, hzw, hwzNe, hpair2]
  have hC2yLeader : sweepLockLeader (C2 y) = true := by
    rw [hC2y]
    exact hC1yLeader
  have hC2yClosed : (C2 y).2 = true := by
    rw [hC2y]
    exact hC1yClosed
  have hC2zLeader : sweepLockLeader (C2 z) = false := by
    rw [hC2z]
    simpa [sweepLockLeader] using hC1zLeader
  have hC2zClosed : (C2 z).2 = true := by
    rw [hC2z]
  have hC2wLeader : sweepLockLeader (C2 w) = true := by
    rw [hC2w]
    simpa [sweepLockLeader] using hC1wLeader
  have hC2wClosed : (C2 w).2 = true := by
    rw [hC2w]
  have hpair3 : P_partialSealSweep (C2 y) (C2 z) =
      (((C2 y).1, false), ((C2 z).1, false)) :=
    P_partialSealSweep_launch (C2 y) (C2 z)
      hC2yLeader hC2yClosed hC2zLeader hC2zClosed
  have hC3z : C3 z = ((C2 z).1, false) := by
    simp [C3, localStep, hyz, hzyNe, hpair3]
  have hC3w : C3 w = C2 w := by
    simp [C3, localStep, hyz, hwyNe, hwzNe]
  have hC3zLeader : sweepLockLeader (C3 z) = false := by
    rw [hC3z]
    simpa [sweepLockLeader] using hC2zLeader
  have hC3zOpen : (C3 z).2 = false := by
    rw [hC3z]
  have hC3wLeader : sweepLockLeader (C3 w) = true := by
    rw [hC3w]
    exact hC2wLeader
  have hC3wClosed : (C3 w).2 = true := by
    rw [hC3w]
    exact hC2wClosed
  have hk1 : sealSweepKillEdge ring C x = false := by
    simp [sealSweepKillEdge, sealSweepKillPair, hxy, hyOpen]
  have hk2 : sealSweepKillEdge ring C1 z = false := by
    simp [sealSweepKillEdge, sealSweepKillPair, hzw, hC1wOpen]
  have hk3 : sealSweepKillEdge ring C2 y = false := by
    simp [sealSweepKillEdge, sealSweepKillPair, hyz, hC2zLeader]
  have hk4 : sealSweepKillEdge ring C3 z = true := by
    simp [sealSweepKillEdge, sealSweepKillPair, hzw,
      hC3zLeader, hC3zOpen, hC3wLeader, hC3wClosed]
  have hcount1 := sealSweepLeaderCount_localStep_exact ring hn C x
  have hcount2 := sealSweepLeaderCount_localStep_exact ring hn C1 z
  have hcount3 := sealSweepLeaderCount_localStep_exact ring hn C2 y
  have hcount4 := sealSweepLeaderCount_localStep_exact ring hn C3 z
  change sealSweepLeaderCount C1 +
      (if sealSweepKillEdge ring C x then 1 else 0) =
    sealSweepLeaderCount C at hcount1
  change sealSweepLeaderCount C2 +
      (if sealSweepKillEdge ring C1 z then 1 else 0) =
    sealSweepLeaderCount C1 at hcount2
  change sealSweepLeaderCount C3 +
      (if sealSweepKillEdge ring C2 y then 1 else 0) =
    sealSweepLeaderCount C2 at hcount3
  change sealSweepLeaderCount C4 +
      (if sealSweepKillEdge ring C3 z then 1 else 0) =
    sealSweepLeaderCount C3 at hcount4
  simp [hk1] at hcount1
  simp [hk2] at hcount2
  simp [hk3] at hcount3
  simp [hk4] at hcount4
  change sealSweepLeaderCount C4 + 1 = sealSweepLeaderCount C
  omega

/-! ## Exact iid one-step numerator -/

/-- Number of directed edges that remove a leader in the current state. -/
def sealSweepKillEdgeCount
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) : Nat :=
  (List.ofFn (fun e : Fin n =>
    if sealSweepKillEdge ring C e then 1 else 0)).sum

/-- The same numerator stated semantically through strict leader-count drop. -/
def sealSweepLeaderDropEdgeCount
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) : Nat :=
  (List.ofFn (fun e : Fin n =>
    if sealSweepLeaderCount
        (localStep ring P_partialSealSweep C e) <
          sealSweepLeaderCount C then 1 else 0)).sum

theorem sealSweepLeaderDropEdgeCount_eq_killEdgeCount
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau) :
    sealSweepLeaderDropEdgeCount ring C =
      sealSweepKillEdgeCount ring C := by
  unfold sealSweepLeaderDropEdgeCount sealSweepKillEdgeCount
  apply congrArg List.sum
  apply congrArg List.ofFn
  funext e
  simp only [sealSweepLeaderCount_localStep_lt_iff ring hn C e]

/-- Boolean target for a drop below the leader count of a fixed block source. -/
def sealSweepLeaderDropTest
    (C : SealSweepConfig n psi kappa tau)
    (D : SealSweepConfig n psi kappa tau) : Bool :=
  decide (sealSweepLeaderCount D < sealSweepLeaderCount C)

theorem sealSweepLeaderDropTest_spec
    (C D : SealSweepConfig n psi kappa tau) :
    sealSweepLeaderDropTest C D = true ↔
      sealSweepLeaderCount D < sealSweepLeaderCount C := by
  simp [sealSweepLeaderDropTest]

private theorem countP_ofFn_eq_sum_indicator
    {m : Nat} {α : Type} (f : Fin m → α) (p : α → Bool) :
    (List.ofFn f).countP p =
      (List.ofFn (fun i => if p (f i) then 1 else 0)).sum := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [List.ofFn_succ, List.ofFn_succ,
        List.countP_cons, List.sum_cons]
      rw [ih]
      cases p (f 0) <;> simp <;> omega

private theorem nodup_ofFn_of_injective
    {q : Nat} {α : Type} (f : Fin q → α)
    (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_ofFn] at hmem
        obtain ⟨i, hi⟩ := hmem
        have h := hf hi
        cases h
      · apply ih
        intro i j hij
        exact Fin.succ_inj.mp (hf hij)

private theorem countP_lower_of_injective_favorable
    {q : Nat} {α : Type} (xs : List α) (p : α → Bool)
    (f : Fin q → α) (hf : Function.Injective f)
    (hmem : ∀ i, f i ∈ xs) (hgood : ∀ i, p (f i) = true) :
    q ≤ xs.countP p := by
  rw [List.countP_eq_length_filter]
  have hnodup := nodup_ofFn_of_injective f hf
  have hsubset : List.ofFn f ⊆ List.filter p xs := by
    intro word hword
    rw [List.mem_ofFn] at hword
    obtain ⟨i, rfl⟩ := hword
    exact (List.mem_filter).2 ⟨hmem i, hgood i⟩
  have hle := hnodup.length_le_of_subset hsubset
  simpa using hle

/-- Exact one-step iid schedule count.  Since the scheduler chooses one of the
`n` directed edges uniformly, this is its drop-probability numerator. -/
theorem sealSweep_oneStepDropCount_eq_killEdgeCount
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau) :
    localHitCount ring P_partialSealSweep
        (sealSweepLeaderDropTest C) C 1 =
      sealSweepKillEdgeCount ring C := by
  rw [← sealSweepLeaderDropEdgeCount_eq_killEdgeCount ring hn C]
  unfold localHitCount sealSweepLeaderDropEdgeCount
  simp only [allSchedules, List.flatMap_cons, List.flatMap_nil,
    List.nil_append, List.append_nil]
  rw [countP_ofFn_eq_sum_indicator]
  simp [hitsWithinLocal, sealSweepLeaderDropTest]

/-- Exact rational form of the one-step conditional iid drift. -/
theorem sealSweep_oneStepDropProbability_eq
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau) :
    localHitProbability ring P_partialSealSweep
        (sealSweepLeaderDropTest C) C 1 =
      (sealSweepKillEdgeCount ring C : Rat) / (n : Rat) := by
  unfold localHitProbability
  rw [sealSweep_oneStepDropCount_eq_killEdgeCount ring hn C,
    allSchedules_length]
  simp

/-! ## Unsafe positive descendants with zero one-step drift -/

theorem exactAlternatingOpen_pointwise
    (m kappa tau : Nat) (i : Fin (2 * m)) :
    exactAlternatingOpen m kappa tau i =
      if i.val % 2 = 0 then exactLU kappa tau else exactFU kappa tau := by
  rw [exactAlternatingOpen, liftMacroConfig,
    alternatingUnsealed_pointwise]
  by_cases h : i.val % 2 = 0
  · simp [h, embedSealMacro, exactLU]
    rfl
  · simp [h, embedSealMacro, exactFU]
    rfl

theorem exactAlternatingOpen_allOpen
    (m kappa tau : Nat) (i : Fin (2 * m)) :
    (exactAlternatingOpen m kappa tau i).2 = false := by
  change (embedSealMacro kappa tau (alternatingUnsealed m i)).2 = false
  rw [embedSealMacro_closed, alternatingUnsealed_pointwise]
  by_cases h : i.val % 2 = 0 <;>
    simp [h, sealMacroSealed]

theorem exactAlternatingOpen_killEdge_false
    (m : Nat) (hm : 0 < m) (kappa tau : Nat)
    (e : Fin (2 * m)) :
    sealSweepKillEdge (evenRing m hm)
        (exactAlternatingOpen m kappa tau) e = false := by
  simp [sealSweepKillEdge, sealSweepKillPair,
    exactAlternatingOpen_allOpen]

theorem exactAlternatingOpen_killEdgeCount_eq_zero
    (m : Nat) (hm : 0 < m) (kappa tau : Nat) :
    sealSweepKillEdgeCount (evenRing m hm)
      (exactAlternatingOpen m kappa tau) = 0 := by
  unfold sealSweepKillEdgeCount
  simp only [exactAlternatingOpen_killEdge_false m hm kappa tau,
    Bool.false_eq_true, if_false]
  change finiteCoordSum (fun _e : Fin (2 * m) => 0) = 0
  exact finiteCoordSum_zero (2 * m)

theorem exactAlternatingOpen_oneStepDropCount_eq_zero
    (m : Nat) (hm : 2 ≤ m) (kappa tau : Nat) :
    localHitCount (evenRing m (by omega)) P_partialSealSweep
        (sealSweepLeaderDropTest
          (exactAlternatingOpen m kappa tau))
        (exactAlternatingOpen m kappa tau) 1 = 0 := by
  rw [sealSweep_oneStepDropCount_eq_killEdgeCount
    (evenRing m (by omega)) (by omega)
    (exactAlternatingOpen m kappa tau)]
  exact exactAlternatingOpen_killEdgeCount_eq_zero
    m (by omega) kappa tau

/-- Exact hostile family for leader-count-only one-step drift. -/
theorem exactAlternatingOpen_unsafe_zero_oneStepDrift
    (m : Nat) (hm : 2 ≤ m) (kappa tau : Nat) :
    let ring := evenRing m (by omega)
    let C := exactAlternatingOpen m kappa tau
    SealSweepPositiveDescendant ring C ∧
      2 ≤ sealSweepLeaderCount C ∧
      ¬ PopulationProtocol.IsSafe
        (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
        ring C isLeaderOutput ∧
      localHitCount ring P_partialSealSweep
        (sealSweepLeaderDropTest C) C 1 = 0 := by
  dsimp only
  have hcap := exact_even_rank_excursion_and_reset m hm kappa tau
  dsimp only at hcap
  have hdesc := hcap.1
  have hunsafe := hcap.2.1
  have hhasLeader :=
    (positiveDescendant_balanced_hasLeader
      (evenRing m (by omega))
      (exactAlternatingOpen m kappa tau) hdesc).2
  have hpositive : 0 < sealSweepLeaderCount
      (exactAlternatingOpen m kappa tau) :=
    (sealSweep_hasLeader_iff_leaderCount_pos _).1 hhasLeader
  have hnotOne : sealSweepLeaderCount
      (exactAlternatingOpen m kappa tau) ≠ 1 := by
    intro hone
    exact hunsafe
      (positiveDescendant_leaderCount_one_isSafe
        (evenRing m (by omega))
        (exactAlternatingOpen m kappa tau) hdesc hone)
  refine ⟨hdesc, by omega, hunsafe, ?_⟩
  exact exactAlternatingOpen_oneStepDropCount_eq_zero
    m hm kappa tau

/-! ## Linearly many explicit four-step collision words in the hostile state -/

/-- For each non-wrapping block `s`, close two adjacent `D,B` pairs, relaunch
the middle pair, and select the resulting `D,A` collision. -/
def exactOpenCollisionWordAt
    (m : Nat) (hm : 3 ≤ m) (s : Fin (m - 2)) :
    List (Fin (2 * m)) :=
  [⟨2 * s.val + 1, by omega⟩,
    ⟨2 * s.val + 3, by omega⟩,
    ⟨2 * s.val + 2, by omega⟩,
    ⟨2 * s.val + 3, by omega⟩]

theorem exactOpenCollisionWordAt_length
    (m : Nat) (hm : 3 ≤ m) (s : Fin (m - 2)) :
    (exactOpenCollisionWordAt m hm s).length = 4 := by
  rfl

theorem exactOpenCollisionWordAt_injective
    (m : Nat) (hm : 3 ≤ m) :
    Function.Injective (exactOpenCollisionWordAt m hm) := by
  intro s t hword
  have hhead := congrArg List.head? hword
  have hfin :
      (⟨2 * s.val + 1, by omega⟩ : Fin (2 * m)) =
        ⟨2 * t.val + 1, by omega⟩ := by
    simpa [exactOpenCollisionWordAt] using hhead
  apply Fin.ext
  have hval := congrArg Fin.val hfin
  change 2 * s.val + 1 = 2 * t.val + 1 at hval
  omega

theorem exactAlternatingOpen_collisionWordAt_drops
    (m : Nat) (hm : 3 ≤ m) (kappa tau : Nat)
    (s : Fin (m - 2)) :
    sealSweepLeaderCount
        (runSchedule
          (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
          (evenRing m (by omega))
          (exactAlternatingOpen m kappa tau)
          (exactOpenCollisionWordAt m hm s)) + 1 =
      sealSweepLeaderCount (exactAlternatingOpen m kappa tau) := by
  let ring := evenRing m (by omega)
  let C := exactAlternatingOpen m kappa tau
  let x : Fin (2 * m) := ⟨2 * s.val + 1, by omega⟩
  let y : Fin (2 * m) := ⟨2 * s.val + 2, by omega⟩
  let z : Fin (2 * m) := ⟨2 * s.val + 3, by omega⟩
  let w : Fin (2 * m) := ⟨2 * s.val + 4, by omega⟩
  have hslt : s.val + 2 < m := by
    have hs := s.isLt
    omega
  have hxy : ring.rightNeighbor x = y := by
    apply Fin.ext
    change (2 * s.val + 1 + 1) % (2 * m) = 2 * s.val + 2
    rw [Nat.mod_eq_of_lt (by omega)]
  have hyz : ring.rightNeighbor y = z := by
    apply Fin.ext
    change (2 * s.val + 2 + 1) % (2 * m) = 2 * s.val + 3
    rw [Nat.mod_eq_of_lt (by omega)]
  have hzw : ring.rightNeighbor z = w := by
    apply Fin.ext
    change (2 * s.val + 3 + 1) % (2 * m) = 2 * s.val + 4
    rw [Nat.mod_eq_of_lt (by omega)]
  have hxyNe : x ≠ y := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [x, y] at hv
    omega
  have hxzNe : x ≠ z := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [x, z] at hv
    omega
  have hxwNe : x ≠ w := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [x, w] at hv
    omega
  have hyzNe : y ≠ z := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [y, z] at hv
    omega
  have hywNe : y ≠ w := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [y, w] at hv
    omega
  have hzwNe : z ≠ w := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [z, w] at hv
    omega
  have hxState : C x = exactFU kappa tau := by
    change exactAlternatingOpen m kappa tau x = exactFU kappa tau
    rw [exactAlternatingOpen_pointwise]
    simp [x]
    rfl
  have hyState : C y = exactLU kappa tau := by
    change exactAlternatingOpen m kappa tau y = exactLU kappa tau
    rw [exactAlternatingOpen_pointwise]
    simp [y]
    rfl
  have hzState : C z = exactFU kappa tau := by
    change exactAlternatingOpen m kappa tau z = exactFU kappa tau
    rw [exactAlternatingOpen_pointwise]
    simp [z]
    rfl
  have hwState : C w = exactLU kappa tau := by
    change exactAlternatingOpen m kappa tau w = exactLU kappa tau
    rw [exactAlternatingOpen_pointwise]
    simp [w]
    rfl
  have hxLeader : sweepLockLeader (C x) = false := by
    rw [hxState]
    rfl
  have hyLeader : sweepLockLeader (C y) = true := by
    rw [hyState]
    rfl
  have hzLeader : sweepLockLeader (C z) = false := by
    rw [hzState]
    rfl
  have hwLeader : sweepLockLeader (C w) = true := by
    rw [hwState]
    rfl
  have hxOpen : (C x).2 = false := by
    simpa [C] using exactAlternatingOpen_allOpen m kappa tau x
  have hyOpen : (C y).2 = false := by
    simpa [C] using exactAlternatingOpen_allOpen m kappa tau y
  have hzOpen : (C z).2 = false := by
    simpa [C] using exactAlternatingOpen_allOpen m kappa tau z
  have hwOpen : (C w).2 = false := by
    simpa [C] using exactAlternatingOpen_allOpen m kappa tau w
  simpa [ring, C, x, y, z, w, exactOpenCollisionWordAt] using
    sealSweep_fourStep_openAlternatingQuad_drop
      ring (by omega) C x y z w hxy hyz hzw
      hxyNe hxzNe hxwNe hyzNe hywNe hzwNe
      hxLeader hxOpen hyLeader hyOpen hzLeader hzOpen hwLeader hwOpen

private theorem hitsWithinLocal_of_final
    {q : Nat} {Q : Type} (ring : DirectedRing q)
    (T : Q → Q → Q × Q) (post : (Fin q → Q) → Bool)
    (C : Fin q → Q) (word : List (Fin q))
    (hfinal : post (runLocalSchedule ring T C word) = true) :
    hitsWithinLocal ring T post C word = true := by
  induction word generalizing C with
  | nil => exact hfinal
  | cons e rest ih =>
      rw [hitsWithinLocal, Bool.or_eq_true]
      exact Or.inr (ih (localStep ring T C e) hfinal)

theorem exactOpenCollisionWordAt_mem_allSchedules
    (m : Nat) (hm : 3 ≤ m) (s : Fin (m - 2)) :
    exactOpenCollisionWordAt m hm s ∈ allSchedules (2 * m) 4 := by
  exact mem_allSchedules_of_length (2 * m) 4
    (exactOpenCollisionWordAt m hm s)
    (exactOpenCollisionWordAt_length m hm s)

theorem exactOpenCollisionWordAt_hits
    (m : Nat) (hm : 3 ≤ m) (kappa tau : Nat)
    (s : Fin (m - 2)) :
    hitsWithinLocal (evenRing m (by omega)) P_partialSealSweep
        (sealSweepLeaderDropTest
          (exactAlternatingOpen m kappa tau))
        (exactAlternatingOpen m kappa tau)
        (exactOpenCollisionWordAt m hm s) = true := by
  apply hitsWithinLocal_of_final
  have hrun :
      runLocalSchedule (evenRing m (by omega)) P_partialSealSweep
          (exactAlternatingOpen m kappa tau)
          (exactOpenCollisionWordAt m hm s) =
        runSchedule
          (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
          (evenRing m (by omega))
          (exactAlternatingOpen m kappa tau)
          (exactOpenCollisionWordAt m hm s) := by
    exact runLocalSchedule_eq_runSchedule
      (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
      (evenRing m (by omega))
      (exactAlternatingOpen m kappa tau)
      (exactOpenCollisionWordAt m hm s)
  rw [hrun]
  apply (sealSweepLeaderDropTest_spec _ _).2
  have hdrop := exactAlternatingOpen_collisionWordAt_drops
    m hm kappa tau s
  omega

/-- There are `m-2` pairwise distinct explicit four-step iid words, and every
one lowers leader count.  This is a scalable favorable-word family, although
a uniform polynomial bound still needs a structural exposure theorem for
arbitrary positive descendants. -/
theorem exactAlternatingOpen_many_distinct_collisionWords
    (m : Nat) (hm : 3 ≤ m) (kappa tau : Nat) :
    Function.Injective (exactOpenCollisionWordAt m hm) ∧
      ∀ s : Fin (m - 2),
        exactOpenCollisionWordAt m hm s ∈ allSchedules (2 * m) 4 ∧
        hitsWithinLocal (evenRing m (by omega)) P_partialSealSweep
          (sealSweepLeaderDropTest
            (exactAlternatingOpen m kappa tau))
          (exactAlternatingOpen m kappa tau)
          (exactOpenCollisionWordAt m hm s) = true := by
  refine ⟨exactOpenCollisionWordAt_injective m hm, ?_⟩
  intro s
  exact ⟨exactOpenCollisionWordAt_mem_allSchedules m hm s,
    exactOpenCollisionWordAt_hits m hm kappa tau s⟩

/-- Exact finite-uniform consequence: already at horizon four the hostile
all-open state has at least `m-2` distinct leader-dropping scheduler words. -/
theorem exactAlternatingOpen_fourStepDropCount_lower
    (m : Nat) (hm : 3 ≤ m) (kappa tau : Nat) :
    m - 2 ≤
      localHitCount (evenRing m (by omega)) P_partialSealSweep
        (sealSweepLeaderDropTest
          (exactAlternatingOpen m kappa tau))
        (exactAlternatingOpen m kappa tau) 4 := by
  unfold localHitCount
  exact countP_lower_of_injective_favorable
    (allSchedules (2 * m) 4)
    (hitsWithinLocal (evenRing m (by omega)) P_partialSealSweep
      (sealSweepLeaderDropTest (exactAlternatingOpen m kappa tau))
      (exactAlternatingOpen m kappa tau))
    (exactOpenCollisionWordAt m hm)
    (exactOpenCollisionWordAt_injective m hm)
    (exactOpenCollisionWordAt_mem_allSchedules m hm)
    (exactOpenCollisionWordAt_hits m hm kappa tau)

/-! ## The first missing finite-window exposure lemma -/

/-- A finite-window form of the missing Markov lemma.  `favorable` is the
required number of iid scheduler words, among `n^horizon`, that strictly lower
the block-source leader count. -/
def SealSweepWindowLeaderDropExposure
    (ring : DirectedRing n) (horizon favorable : Nat) : Prop :=
  ∀ C : SealSweepConfig n psi kappa tau,
    SealSweepPositiveDescendant ring C →
    2 ≤ sealSweepLeaderCount C →
    favorable ≤ localHitCount ring P_partialSealSweep
      (sealSweepLeaderDropTest C) C horizon

/-- Horizon one cannot supply even one favorable word uniformly.  Any useful
coalescence proof must establish exposure over a longer window and count many
ways to create/select a kill edge. -/
theorem not_windowOne_one_leaderDropExposure_even
    (m : Nat) (hm : 2 ≤ m) (kappa tau : Nat) :
    ¬ SealSweepWindowLeaderDropExposure
      (psi := OverlayNoGoPsi) (kappa := kappa) (tau := tau)
      (evenRing m (by omega)) 1 1 := by
  intro hexposure
  have hhostile := exactAlternatingOpen_unsafe_zero_oneStepDrift
    m hm kappa tau
  dsimp only at hhostile
  have hbound := hexposure
    (exactAlternatingOpen m kappa tau) hhostile.1 hhostile.2.1
  rw [hhostile.2.2.2] at hbound
  omega

end PPartialSealSweepIidCoalescenceBarrierSol
end PPLLCompleteMultiLeaderCleanup
