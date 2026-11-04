import Leader.Wu.Protocol.BoundedProtocol
import Leader.Wu.Scheduler.ExplicitOneOverNSSLE
import Leader.Wu.Safety.IsSafeReflection
import Init.Data.Fin.Lemmas

set_option autoImplicit false
set_option Elab.async false

/-!
# The bounded-protocol route, conditional on pointwise safety reachability

This file concerns exactly `PPLLRepair.boundedProtocol`: the finite-carrier
presentation of the saturating no-collision transition. It does not establish
any convergence theorem for `PPLL.protocol` or for all raw `AgentState` values.

The final theorem constructs the configuration enumeration and the positive
uniform schedule-length bound. Its remaining mathematical premise is `hpoint`:
every nonsafe bounded configuration admits a finite schedule to genuine
`PopulationProtocol.IsSafe`. Finiteness does not prove that premise, and this
file makes no claim that the premise holds at n = 4.

Both the selected words and the supplied safety reflection use classical
reasoning. No executable safety test or parameter-only running-time estimate
is claimed.
-/

namespace ZZBoundedRoute

open PPLLResearchFormulation

/-- Step 1: specialize the existing headline theorem to the bounded protocol.
The Boolean reflection obligation is discharged internally. -/
theorem bounded_explicitOneOverNSSLE_of_producer
    {ψ κ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (hn2 : 1 < n) (L : Nat) (hL : 0 < L)
    (hproducer :
      ∀ C : (PPLLRepair.boundedProtocol hψ κ).Configuration n,
        ¬ PopulationProtocol.IsSafe
          (PPLLRepair.boundedProtocol hψ κ) ring C isLeaderOutput →
        ∃ w : DetSchedule n,
          w.length ≤ L ∧
          PopulationProtocol.IsSafe
            (PPLLRepair.boundedProtocol hψ κ) ring
            (runLocalSchedule ring
              (PPLLRepair.boundedProtocol hψ κ).transition C w)
            isLeaderOutput) :
    let k := (n - 1) * (n ^ L - 1) + 1
    UniformOneOverNFailureAtHorizon
      (PPLLRepair.boundedProtocol hψ κ) ring isLeaderOutput 1 (k * L) := by
  exact
    PPLLClosedDomainSchedulerAmplificationSol.boundedIsSafeProducer_explicitOneOverNSSLE
      (PPLLRepair.boundedProtocol hψ κ) ring isLeaderOutput
      (ZZIsSafeDecidable.isSafeBool
        (PPLLRepair.boundedProtocol hψ κ) ring isLeaderOutput)
      (ZZIsSafeDecidable.isSafeBool_hdec
        (PPLLRepair.boundedProtocol hψ κ) ring isLeaderOutput)
      hn2 L hL hproducer

/-- Every value represented in a finite list is bounded by its folded maximum.
No duplicate-freedom or decidable equality is required. -/
private theorem le_foldr_max_of_mem
    {Q : Type} (f : Q → Nat) (xs : List Q) :
    ∀ x : Q, x ∈ xs →
      f x ≤ xs.foldr (fun y b => Nat.max (f y) b) 0 := by
  induction xs with
  | nil =>
      intro x hx
      cases hx
  | cons y ys ih =>
      intro x hx
      change f x ≤ Nat.max (f y)
        (ys.foldr (fun z b => Nat.max (f z) b) 0)
      rcases List.mem_cons.mp hx with hxy | hx
      · subst x
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih x hx) (Nat.le_max_right _ _)

/-- Step 2: pointwise safety reachability on an exhaustively listed
configuration type supplies a positive uniform word-length bound. -/
theorem uniformL_of_pointwise_bounded
    {ψ κ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (e : ExhaustiveList
      ((PPLLRepair.boundedProtocol hψ κ).Configuration n))
    (hpoint :
      ∀ C : (PPLLRepair.boundedProtocol hψ κ).Configuration n,
        ¬ PopulationProtocol.IsSafe
          (PPLLRepair.boundedProtocol hψ κ) ring C isLeaderOutput →
        ∃ w : DetSchedule n,
          PopulationProtocol.IsSafe
            (PPLLRepair.boundedProtocol hψ κ) ring
            (runLocalSchedule ring
              (PPLLRepair.boundedProtocol hψ κ).transition C w)
            isLeaderOutput) :
    ∃ L : Nat, 0 < L ∧
      ∀ C : (PPLLRepair.boundedProtocol hψ κ).Configuration n,
        ¬ PopulationProtocol.IsSafe
          (PPLLRepair.boundedProtocol hψ κ) ring C isLeaderOutput →
        ∃ w : DetSchedule n,
          w.length ≤ L ∧
          PopulationProtocol.IsSafe
            (PPLLRepair.boundedProtocol hψ κ) ring
            (runLocalSchedule ring
              (PPLLRepair.boundedProtocol hψ κ).transition C w)
            isLeaderOutput := by
  classical
  let P : PopulationProtocol := PPLLRepair.boundedProtocol hψ κ
  let Safe : P.Configuration n → Prop :=
    fun C => PopulationProtocol.IsSafe P ring C isLeaderOutput
  have hwords : ∀ C : P.Configuration n,
      ∃ w : DetSchedule n,
        Safe (runLocalSchedule ring P.transition C w) := by
    intro C
    by_cases hs : Safe C
    · exact ⟨[], hs⟩
    · exact hpoint C hs
  let pick : (C : P.Configuration n) →
      { w : DetSchedule n //
        Safe (runLocalSchedule ring P.transition C w) } :=
    fun C => Classical.choice (by
      obtain ⟨w, hw⟩ := hwords C
      exact ⟨⟨w, hw⟩⟩)
  let M : Nat :=
    e.values.foldr (fun C b => Nat.max (pick C).val.length b) 0
  refine ⟨M + 1, by omega, ?_⟩
  intro C _hnot
  refine ⟨(pick C).val, ?_, (pick C).property⟩
  have hbound : (pick C).val.length ≤ M :=
    le_foldr_max_of_mem
      (fun D : P.Configuration n => (pick D).val.length)
      e.values C (e.complete C)
  omega

/-- Step 3: enumerate all functions on `Fin n` from a local exhaustive list.
The successor decoder is the head/tail constructor `Fin.cases`. -/
def exhaustiveFinFunctions {Q : Type} (e : ExhaustiveList Q) :
    (n : Nat) → ExhaustiveList (Fin n → Q)
  | 0 =>
      { values := [fun i : Fin 0 => (Fin.elim0 i : Q)]
        complete := by
          intro f
          apply List.mem_singleton.mpr
          funext i
          exact Fin.elim0 i }
  | n + 1 =>
      ExhaustiveList.mapSurjective
        (ExhaustiveList.prod e (exhaustiveFinFunctions e n))
        (fun p : Q × (Fin n → Q) =>
          fun i : Fin (n + 1) => Fin.cases p.1 p.2 i)
        (by
          intro f
          refine ⟨(f 0, fun j => f j.succ), ?_⟩
          funext i
          refine Fin.cases ?_ ?_ i
          · rfl
          · intro j
            rfl)

/-- The actual configuration certificate needed by step 2, with no
additional enumeration hypothesis. -/
def boundedConfigurationCertificate
    {ψ : Nat} (hψ : ψ > 0) (κ n : Nat) :
    ExhaustiveList ((PPLLRepair.boundedProtocol hψ κ).Configuration n) :=
  exhaustiveFinFunctions
    (PPLLRepair.boundedProtocolStateCertificate hψ κ) n

/-- End-to-end conditional result for the bounded protocol.
Only pointwise safety reachability and the explicit parameter conditions
remain as hypotheses; the list, uniform bound, and safety reflection are
supplied by the preceding constructions. -/
theorem bounded_explicitOneOverNSSLE_of_pointwise
    {ψ κ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (hn2 : 1 < n)
    (hpoint :
      ∀ C : (PPLLRepair.boundedProtocol hψ κ).Configuration n,
        ¬ PopulationProtocol.IsSafe
          (PPLLRepair.boundedProtocol hψ κ) ring C isLeaderOutput →
        ∃ w : DetSchedule n,
          PopulationProtocol.IsSafe
            (PPLLRepair.boundedProtocol hψ κ) ring
            (runLocalSchedule ring
              (PPLLRepair.boundedProtocol hψ κ).transition C w)
            isLeaderOutput) :
    ∃ L : Nat, 0 < L ∧
      UniformOneOverNFailureAtHorizon
        (PPLLRepair.boundedProtocol hψ κ) ring isLeaderOutput 1
        (((n - 1) * (n ^ L - 1) + 1) * L) := by
  obtain ⟨L, hL, hproducer⟩ :=
    uniformL_of_pointwise_bounded (κ := κ) hψ ring
      (boundedConfigurationCertificate hψ κ n) hpoint
  refine ⟨L, hL, ?_⟩
  exact bounded_explicitOneOverNSSLE_of_producer
    (κ := κ) hψ ring hn2 L hL hproducer

end ZZBoundedRoute

#print axioms ZZBoundedRoute.bounded_explicitOneOverNSSLE_of_producer
#print axioms ZZBoundedRoute.uniformL_of_pointwise_bounded
#print axioms ZZBoundedRoute.exhaustiveFinFunctions
#print axioms ZZBoundedRoute.boundedConfigurationCertificate
#print axioms ZZBoundedRoute.bounded_explicitOneOverNSSLE_of_pointwise
