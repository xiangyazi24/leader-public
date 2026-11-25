import Leader.L4.Height.G9DotProduction
import Leader.L4.WindowCappedPublic

namespace L4.Height.G9Dot
open L4.AllSizeProtocol L4.PhysicalCustody L4.Compiler.Native
open L4.Height.G9Wire L4.Height.G9Wire.CustodySpec L4.Height.G9Wire.PublicSpec
open L4.Height.G9Spine

/-- The named uniform production coefficient, with no existential size
dependence. Keep the constants symbolic while checking composition. -/
noncomputable def production_coefficient : Nat :=
  timeCoeff L4.PhysicalCustodyProduction.K_custody (2^32)
    (patrolAllowance L4.PhysicalPublic.cpub)

theorem deployed_at_coefficients (g C : Nat)
    (hCust : ∀ {s n}, 4≤n → 6≤s → s=ell (ell n) →
      ∀ x : Raw s n, IIDExpectedHittingTimeAtMost (rawNext s) Custody x (packingCoefficient g*n^2))
    (hPack : ∀ {s n}, 4≤n → ∀ x : Raw s n, Marked x →
      IIDExpectedHittingTimeAtMost (rawNext s) PackedElected x (C*n^2))
    (hBound : ∀ {n}, 4≤n → n≤boundedN → ∀ x : BoundedRaw n,
      IIDExpectedHittingTimeAtMost boundedNext BoundedElected x (C*n^2)) :
    ∀ n (hn : 4≤n),
      (deployment (ceilingLogTwo (ceilingLogTwo n))).Expected
        boundedEncode boundedDecode n hn g (patrolAllowance C) := by
  intro n hn
  let s := ceilingLogTwo (ceilingLogTwo n)
  change (deployment s).Expected boundedEncode boundedDecode n hn g (patrolAllowance C)
  have ha : s = ell (ell n) := rfl
  by_cases hs : 6≤s
  · rw [deployment,if_pos hs]
    intro x
    exact physical_expected _ hn
      (packed_interfaces hn hs ha g C (hCust hn hs ha) production_service packed_quiet
        actual_display actual_observer (hPack hn)) x
  · rw [deployment,if_neg hs]
    have hb : n≤boundedN := Nat.le_of_not_gt (fun h=>hs ((packed_advice_iff n).2 h))
    intro x
    exact physical_expected _ hn
      (bounded_interfaces boundedEncode boundedDecode hn hb g C (hBound hn hb)) x

theorem all_sizes_expected_at_production_coefficient :
    ∀ n (hn : 4≤n),
      (deployment (ceilingLogTwo (ceilingLogTwo n))).Expected
        boundedEncode boundedDecode n hn L4.PhysicalCustodyProduction.K_custody
          (patrolAllowance L4.PhysicalPublic.cpub) :=
  deployed_at_coefficients L4.PhysicalCustodyProduction.K_custody L4.PhysicalPublic.cpub
    (fun {_ _} _ hs ha x => (L4.MonitorRawBridge.height_iff_row _ _ _ _).mpr
      (L4.PhysicalCustodyProduction.custody_reached ha hs x))
    L4.PhysicalPublic.packed_suffix_at_cpub L4.PhysicalPublic.bounded_suffix_at_cpub

theorem allSize_fast :
    ∀ n (hn : 4≤n),
      (deployment (ceilingLogTwo (ceilingLogTwo n))).Expected
        boundedEncode boundedDecode n hn L4.PhysicalCustodyProduction.K_custody
          (patrolAllowance L4.PhysicalPublic.cpub) :=
  all_sizes_expected_at_production_coefficient


private abbrev compactD (s : Nat) : Deployment := .compactPacked s
private abbrev CompactRaw (s n : Nat) := Fin n → (compactD s).Site
private def compactProject {s n : Nat} (x : Raw s n) : CompactRaw s n :=
  fun i => PackedCore.project (x i)
private def compactLift {s n : Nat} (x : CompactRaw s n) : Raw s n :=
  fun i => PackedCore.lift (x i)

private noncomputable def compactNext (s : Nat) {n : Nat} (hn : 0<n) :
    CompactRaw s n → Fin n → CompactRaw s n :=
  PopulationProtocol.step
    ⟨(compactD s).Site, Bool, (fun a b => (compactD s).row boundedEncode boundedDecode (a,b)),
      (compactD s).leader boundedDecode⟩ (⟨hn⟩ : DirectedRing n)

theorem compact_step_projects {s n : Nat} (hn : 0<n) (x : Raw s n) (e : Fin n) :
    compactProject (rawNext s x e) = compactNext s hn (compactProject x) e := by
  funext i
  let r := L4.rightNeighbor e
  have H := PackedCore.pair_projects (rows s) (x e,x r)
  change PackedCore.project
      (if i=e then (largePair (rows s) (x e,x r)).1
        else if i=r then (largePair (rows s) (x e,x r)).2 else x i) =
    (if i=e then (PackedCore.pair (rows s) (compactProject x e,compactProject x r)).1
        else if i=r then (PackedCore.pair (rows s) (compactProject x e,compactProject x r)).2
        else compactProject x i)
  by_cases he : i=e
  · simpa only [if_pos he,Pair.map,compactProject] using congrArg Prod.fst H
  · by_cases hr : i=r
    · simpa only [if_neg he,if_pos hr,Pair.map,compactProject] using congrArg Prod.snd H
    · simp only [if_neg he,if_neg hr,compactProject]

theorem compact_run_projects {s n : Nat} (hn : 0<n) (x : Raw s n)
    (w : List (Fin n)) :
    compactProject (runWord (rawNext s) x w) =
      runWord (compactNext s hn) (compactProject x) w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    change compactProject (runWord (rawNext s) (rawNext s x e) w) =
      runWord (compactNext s hn) (compactNext s hn (compactProject x) e) w
    rw [ih,compact_step_projects]

theorem compact_reference_iff {s n : Nat} (hn : 0<n) (x : Raw s n) :
    Permanent (rawNext s) (fun y i => packedRead s (y i)) x ↔
      Permanent (compactNext s hn) (fun y i => (compactD s).leader boundedDecode (y i))
        (compactProject x) := by
  have h (w : List (Fin n)) (i : Fin n) :
      (compactD s).leader boundedDecode
        (runWord (compactNext s hn) (compactProject x) w i) =
        packedRead s (runWord (rawNext s) x w i) := by
    rw [← compact_run_projects]
    change H5.seesReference (reference (rows s)
      (PackedCore.lift (PackedCore.project (runWord (rawNext s) x w i)))) =
      H5.seesReference (reference (rows s) (runWord (rawNext s) x w i))
    rw [PackedCore.reference_projects]
  unfold Permanent
  simp only [h]

theorem packed_reference_at_production_coefficients {s n : Nat}
    (hn : 4≤n) (hs : 6≤s) (ha : s=ell (ell n)) (x : Raw s n) :
    IIDExpectedHittingTimeAtMost (rawNext s)
      (Permanent (rawNext s) (fun y i => packedRead s (y i))) x
      ((L4.PhysicalCustodyProduction.K_custody + 2^(5*(2^32 : Nat)+65))*n^2) := by
  have hp := (packed_advice_iff n).1 (ha ▸ hs)
  have hc := (L4.MonitorRawBridge.height_iff_row _ _ _ _).mpr
    (L4.PhysicalCustodyProduction.custody_reached ha hs x)
  exact packed_reference_expected _ (by omega)
    (packed_display_inputs hn hs ha production_service packed_quiet actual_display) hp x hc

theorem compact_allSize_fast :
    ∀ n (hn : 4≤n),
      (compactDeployment (ceilingLogTwo (ceilingLogTwo n))).Expected
        boundedEncode boundedDecode n hn L4.PhysicalCustodyProduction.K_custody
          (patrolAllowance L4.WindowCappedPublic.coefficient) := by
  intro n hn
  let s := ceilingLogTwo (ceilingLogTwo n)
  change (compactDeployment s).Expected boundedEncode boundedDecode n hn
    L4.PhysicalCustodyProduction.K_custody (patrolAllowance L4.WindowCappedPublic.coefficient)
  by_cases hs : 6≤s
  · rw [compactDeployment,if_pos hs]
    intro x
    have pos : 0<n := by omega
    apply (iid_expected_iff_leader _ _ pos _ _).1
    let f : Raw s n → CompactRaw s n := compactProject
    let next := compactNext s pos
    let P := Permanent next (fun y i => (compactD s).leader boundedDecode (y i))
    have hx : f (compactLift x) = x := funext fun _ => PackedCore.project_lift _
    have hT : (fun z => P (f z)) =
        Permanent (rawNext s) (fun y i => packedRead s (y i)) :=
      funext fun z => propext (compact_reference_iff pos z).symm
    have hp := packed_reference_at_production_coefficients hn hs rfl (compactLift x)
    rw [← hT] at hp
    have hp' : IIDExpectedHittingTimeAtMost next P x
        ((L4.PhysicalCustodyProduction.K_custody + 2^(5*(2^32 : Nat)+65))*n^2) := by
      intro t
      change Height.iidHitCost next P t x ≤
        ((L4.PhysicalCustodyProduction.K_custody + 2^(5*(2^32 : Nat)+65))*n^2)*n^t
      rw [← hx, ← projection_cost f (rawNext s) next (compact_step_projects pos) P t (compactLift x)]
      exact hp t
    exact expected_bound_mono next P x hp' (Nat.mul_le_mul_right _ (Nat.le_max_left _ _))
  · rw [compactDeployment,if_neg hs]
    have hb : n≤boundedN := Nat.le_of_not_gt (fun h => hs ((packed_advice_iff n).2 h))
    intro x
    have pos : 0<n := by omega
    apply (iid_expected_iff_leader _ _ pos _ _).1
    let P := Permanent (boundedNext : BoundedRaw n → Fin n → BoundedRaw n)
      (boundedLeaderWith boundedDecode)
    have htarget : (L4.BoundedPublicCodec.BoundedElected : BoundedRaw n → Prop) = P :=
      funext fun y => propext (productSafe_iff_permanent boundedNext
        (boundedLeaderWith boundedDecode) y)
    have h := L4.WindowCappedPublic.bounded_suffix_at_coefficient hn hb x
    rw [htarget] at h
    exact expected_bound_mono _ _ _ h
      (Nat.le_trans (public_budget L4.WindowCappedPublic.coefficient n)
        (Nat.mul_le_mul_right _ (Nat.le_max_right _ _)))

#print axioms compact_step_projects
#print axioms compact_run_projects
#print axioms packed_reference_at_production_coefficients
#print axioms compact_allSize_fast

#print axioms allSize_fast
#print axioms production_coefficient
#print axioms all_sizes_expected_at_production_coefficient
end L4.Height.G9Dot
