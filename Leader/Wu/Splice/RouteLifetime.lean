import Leader.Wu.Splice.CheckStickyGate
import Leader.Wu.Splice.LeaseLifetime

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9RouteLifetime

open PPLL PPLLRepair PPLLResearchFormulation
open B9SpliceControllerR1TableV6
open B9CheckXSupplierDesign
open B9CheckRouteLifecycle
open B9CheckStickyGate
open FiniteUniformStoppingTree

variable {n psi kappa tau : Nat}

private instance instDecidableRouteWriterGateShapeLife
    (u : R1AgentStateV6 psi kappa tau) :
    Decidable (RouteWriterGateShape u) := by
  unfold RouteWriterGateShape
  infer_instance

/-- The tracked sticky gate has disappeared. -/
def RouteGateReleasedAt
    (site : Fin n) (S : XSupplierConfig n psi kappa tau) : Prop :=
  ¬ RouteWriterGateShape (S site).splice

private instance instDecidableRouteGateReleasedAt
    (site : Fin n) (S : XSupplierConfig n psi kappa tau) :
    Decidable (RouteGateReleasedAt site S) := by
  unfold RouteGateReleasedAt
  infer_instance

/-- Finite-word lifetime of one sticky gate.  `S` is the post-ARM state.
The step is explicit because current main has not yet packaged the V10 normal
row, comparison-cleanup handoff and reverse sweep into one global scheduler
step.  An unresolved supplied word receives the sentinel `|u|+1`. -/
def routeLife
    (step : XSupplierConfig n psi kappa tau -> Fin n ->
      XSupplierConfig n psi kappa tau)
    (site : Fin n) :
    XSupplierConfig n psi kappa tau -> List (Fin n) -> Nat
  | S, [] => if RouteGateReleasedAt site S then 0 else 1
  | S, a :: u =>
      if RouteGateReleasedAt site S then 0
      else 1 + routeLife step site (step S a) u

/-- Success indicator for one finite raw scheduler word. -/
def routeResolutionWeight
    (step : XSupplierConfig n psi kappa tau -> Fin n ->
      XSupplierConfig n psi kappa tau)
    (site : Fin n) (S : XSupplierConfig n psi kappa tau)
    (u : List (Fin n)) : Nat :=
  if routeLife step site S u <= u.length then 1 else 0

/-- Exact finite-horizon scheduler-word success numerator. -/
def routeResolutionMass
    (step : XSupplierConfig n psi kappa tau -> Fin n ->
      XSupplierConfig n psi kappa tau)
    (site : Fin n) (S : XSupplierConfig n psi kappa tau)
    (L : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n L
    (routeResolutionWeight step site S)

/-- The local retry condition needed for the one-letter release block. -/
def RouteOneLetterReady
    (step : XSupplierConfig n psi kappa tau -> Fin n ->
      XSupplierConfig n psi kappa tau)
    (site : Fin n) (S : XSupplierConfig n psi kappa tau) : Prop :=
  RouteGateReleasedAt site S ∨
    ∃ e : Fin n, RouteGateReleasedAt site (step S e)

/-- Constants for the post-handoff one-gate release leaf. -/
def routeReleaseBlockLength : Nat := 1

def routeReleaseBlockQ (n : Nat) : Nat := n

/-- A concrete V10 reverse-release write turns a left gate into the distinct
release-token code point, hence the gate is gone at that site. -/
theorem routeReleaseWriteV10_left_released
    (l r : R1AgentStateV6 psi kappa tau)
    (hg : RouteWriterGateShape l) :
    ¬ RouteWriterGateShape (routeReleaseWriteV10 l r).1 := by
  have ht : RouteReleaseTokenShapeV9
      (routeReleaseWriteV10 l r).1 := by
    simp [routeReleaseWriteV10,
      B9CheckRouteLifecycle.routeReleaseWriteV9, hg]
  intro hgate
  exact (release_token_disjoint_route_gate
    (routeReleaseWriteV10 l r).1) ⟨ht, hgate⟩

private theorem ofFn_zero_sum (m : Nat) :
    (List.ofFn (fun _ : Fin m => 0)).sum = 0 := by
  simpa using PPLLEpochVoterSumTools.sum_ofFn_const m 0

private theorem ofFn_indicator_sum_one
    {m : Nat} (a : Fin m) :
    (List.ofFn (fun i : Fin m => if i = a then 1 else 0)).sum = 1 := by
  have h := PPLLEpochVoterSumTools.sum_ofFn_balance_one
    (fun i : Fin m => if i = a then 1 else 0)
    (fun _ : Fin m => 0) a (by
      intro i hia
      simp [hia])
  have hz := ofFn_zero_sum m
  rw [hz] at h
  simpa using h

private theorem wordSum_zero
    {m : Nat} (f : List (Fin m) -> Nat) :
    FixedSpanRenewalPayload.wordSum m 0 f = f [] := by
  rfl

/-- One specified releasing letter contributes one unit of raw success mass. -/
theorem routeResolutionMass_pos_of_letter
    (step : XSupplierConfig n psi kappa tau -> Fin n ->
      XSupplierConfig n psi kappa tau)
    (site : Fin n) (S : XSupplierConfig n psi kappa tau)
    (e : Fin n)
    (hrelease : RouteGateReleasedAt site S ∨
      RouteGateReleasedAt site (step S e)) :
    1 <= routeResolutionMass step site S 1 := by
  have hw : routeResolutionWeight step site S [e] = 1 := by
    rcases hrelease with hs | ht
    · simp [routeResolutionWeight, routeLife, hs]
    · by_cases hs : RouteGateReleasedAt site S
      · simp [routeResolutionWeight, routeLife, hs]
      · simp [routeResolutionWeight, routeLife, hs, ht]
  unfold routeResolutionMass
  rw [show (1 : Nat) = 0 + 1 by rfl,
    FixedSpanRenewalPayload.wordSum_succ]
  rw [← ofFn_indicator_sum_one e]
  rw [Nat.zero_add]
  apply PPLLEpochVoterSumTools.sum_ofFn_le
  intro a
  rw [wordSum_zero]
  by_cases ha : a = e
  · subst a
    simp [hw]
  · simp [ha]

/-- Project word-sum HMass form for the release-ready one-gate tail:
`L = 1`, `Q = n`. -/
theorem routeResolutionHMass_of_oneLetterReady
    (step : XSupplierConfig n psi kappa tau -> Fin n ->
      XSupplierConfig n psi kappa tau)
    (site : Fin n) (S : XSupplierConfig n psi kappa tau)
    (hready : RouteOneLetterReady step site S) :
    n ^ 1 <= n *
      FixedSpanRenewalPayload.wordSum n 1
        (routeResolutionWeight step site S) := by
  have hm : 1 <= routeResolutionMass step site S 1 := by
    rcases hready with hs | ⟨e, he⟩
    · exact routeResolutionMass_pos_of_letter
        (step := step) (site := site) S site (Or.inl hs)
    · exact routeResolutionMass_pos_of_letter
        (step := step) (site := site) S e (Or.inr he)
  have h := Nat.mul_le_mul_left n hm
  simpa [routeResolutionMass] using h

/-- One raw letter is one macro block.  Released gates absorb in success;
unreleased non-releasing letters retry from their actual endpoint. -/
def routeBlockStep
    (step : XSupplierConfig n psi kappa tau -> Fin n ->
      XSupplierConfig n psi kappa tau)
    (site : Fin n) (S : XSupplierConfig n psi kappa tau)
    (e : Fin n) : StopNode (XSupplierConfig n psi kappa tau) :=
  if RouteGateReleasedAt site S then .success
  else
    let T := step S e
    if RouteGateReleasedAt site T then .success else .active T

/-- Exact geometric tail requested for the release-ready regime.  This is the
next theorem once cleanup proves the one-letter-ready condition uniformly on
all active retry states. -/
def RouteOneLetterGeometricTailBound
    (step : XSupplierConfig n psi kappa tau -> Fin n ->
      XSupplierConfig n psi kappa tau)
    (site : Fin n) (S : XSupplierConfig n psi kappa tau) : Prop :=
  ∀ k,
    n ^ k *
        activeCount
          (UniformBlockRenewal.retry (routeBlockStep step site))
          (.active S) k <=
      (n - 1) ^ k * n ^ k

end B9RouteLifetime

#print axioms B9RouteLifetime.routeReleaseWriteV10_left_released
#print axioms B9RouteLifetime.routeResolutionMass_pos_of_letter
#print axioms B9RouteLifetime.routeResolutionHMass_of_oneLetterReady
