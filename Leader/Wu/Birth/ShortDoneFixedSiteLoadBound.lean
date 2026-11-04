import Leader.Wu.Birth.ShortDoneFixedSiteConsumer
import Leader.Wu.Birth.ShortDoneParticipationLoadBound


namespace BirthShortDoneFixedSiteLoadBound


open PPLL PPLLResearchFormulation
open BirthShortDoneParticipationBudget
open BirthShortDoneParticipationLoadMass
open BirthShortDoneParticipationLoadBound
open BirthShortDoneFixedSiteConsumer


set_option autoImplicit false
set_option pp.structureInstances false


variable {n ψ width κ τ T Q : Nat}


/-- Exact factorial/binomial scaling for one actual fresh physical site.
Every other initial state and timer is unrestricted. -/
theorem actual_fixed_site_scaled
    (hn2 : 2 ≤ n) (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (ring : DirectedRing n)
    (C : Fin n → Local ψ κ τ) (i : Fin n) (T : Nat)
    (hfresh : (C i).stall.val = τ) :
    n ^ (τ + 1) *
        actualZeroServiceNumerator hψ hwidth hle ring C i T ≤
      n ^ T * (chooseCount T (τ + 1) * 2 ^ (τ + 1)) := by
  calc
    n ^ (τ + 1) *
          actualZeroServiceNumerator hψ hwidth hle ring C i T ≤
        n ^ (τ + 1) * overloadNumerator ring i T (τ + 1) :=
      Nat.mul_le_mul_left _
        (actual_zeroServiceNumerator_le_overload
          (κ := κ) (τ := τ) hψ hwidth hle ring C i T hfresh)
    _ ≤ n ^ T * (chooseCount T (τ + 1) * 2 ^ (τ + 1)) :=
      fixed_node_scaled hn2 ring i T (τ + 1)


/-- Exact sufficient fixed-site exposure inequality. -/
theorem actual_fixed_site_exposure_crossmul
    (hn2 : 2 ≤ n) (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (ring : DirectedRing n)
    (C : Fin n → Local ψ κ τ) (i : Fin n) (T Q : Nat)
    (hfresh : (C i).stall.val = τ)
    (hscale :
      Q * (chooseCount T (τ + 1) * 2 ^ (τ + 1)) ≤ n ^ (τ + 1)) :
    Q * actualZeroServiceNumerator hψ hwidth hle ring C i T ≤ n ^ T := by
  calc
    Q * actualZeroServiceNumerator hψ hwidth hle ring C i T ≤
        Q * overloadNumerator ring i T (τ + 1) :=
      Nat.mul_le_mul_left Q
        (actual_zeroServiceNumerator_le_overload
          (κ := κ) (τ := τ) hψ hwidth hle ring C i T hfresh)
    _ ≤ n ^ T :=
      fixed_node_exposure_crossmul hn2 ring i T (τ + 1) Q hscale


/-- Multiplicity union numerator for exactly the caller-listed physical sites. -/
def listedActualZeroServiceMass
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → Local ψ κ τ)
    (sites : List (Fin n)) (T : Nat) : Nat :=
  (sites.map (fun i =>
    actualZeroServiceNumerator hψ hwidth hle ring C i T)).sum


/-- Only listed sites need initial fresh credit.  Duplicate entries are a
conservative repeated union charge, matching `listedSiteOverloadMass`. -/
theorem listed_actual_le_overload
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → Local ψ κ τ)
    (sites : List (Fin n)) (T : Nat)
    (hfresh : ∀ i, i ∈ sites → (C i).stall.val = τ) :
    listedActualZeroServiceMass hψ hwidth hle ring C sites T ≤
      listedSiteOverloadMass ring sites T (τ + 1) := by
  revert hfresh
  induction sites with
  | nil =>
      intro hfresh
      simp [listedActualZeroServiceMass, listedSiteOverloadMass]
  | cons i sites ih =>
      intro hfresh
      have hi : (C i).stall.val = τ := hfresh i (by simp)
      have htail : ∀ j, j ∈ sites → (C j).stall.val = τ := by
        intro j hj
        exact hfresh j (by simp [hj])
      have hhead := actual_zeroServiceNumerator_le_overload
        (κ := κ) (τ := τ) hψ hwidth hle ring C i T hi
      have hrest := ih htail
      simpa [listedActualZeroServiceMass, listedSiteOverloadMass] using
        Nat.add_le_add hhead hrest


/-- Finite fixed-list union exposure.  No factor n is inserted: the only
multiplicity is the actual `sites.length`. -/
theorem listed_actual_exposure_crossmul
    (hn2 : 2 ≤ n) (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (ring : DirectedRing n)
    (C : Fin n → Local ψ κ τ) (sites : List (Fin n)) (T Q : Nat)
    (hfresh : ∀ i, i ∈ sites → (C i).stall.val = τ)
    (hscale :
      Q * sites.length * (chooseCount T (τ + 1) * 2 ^ (τ + 1)) ≤
        n ^ (τ + 1)) :
    Q * listedActualZeroServiceMass hψ hwidth hle ring C sites T ≤
      n ^ T := by
  calc
    Q * listedActualZeroServiceMass hψ hwidth hle ring C sites T ≤
        Q * listedSiteOverloadMass ring sites T (τ + 1) :=
      Nat.mul_le_mul_left Q
        (listed_actual_le_overload hψ hwidth hle ring C sites T hfresh)
    _ ≤ n ^ T :=
      listed_sites_exposure_crossmul hn2 ring sites T (τ + 1) Q hscale


/-- `τ = 0`: freshness is automatic because every stall is `Fin 1`.
The exact sufficient arithmetic condition is the order-one specialization. -/
theorem actual_tau_zero_exposure_crossmul
    (hn2 : 2 ≤ n) (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (ring : DirectedRing n)
    (C : Fin n → Local ψ κ 0) (i : Fin n) (T Q : Nat)
    (hscale : Q * (chooseCount T 1 * 2) ≤ n) :
    Q * actualZeroServiceNumerator hψ hwidth hle ring C i T ≤ n ^ T := by
  calc
    Q * actualZeroServiceNumerator hψ hwidth hle ring C i T ≤
        Q * overloadNumerator ring i T 1 :=
      Nat.mul_le_mul_left Q
        (actual_tau_zero_badMass_le_overload
          (κ := κ) hψ hwidth hle ring C i T)
    _ ≤ n ^ T := by
      apply fixed_node_exposure_crossmul hn2 ring i T 1 Q
      simpa using hscale


/-- `n = 1` alias boundary: use the exact one-charge-per-edge count, not the
`n ≥ 2` two-endpoint factorial cap. -/
theorem ring1_alias_exposure_crossmul
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing 1) (C : Fin 1 → Local ψ κ τ)
    (i : Fin 1) (T Q : Nat) (hfresh : (C i).stall.val = τ)
    (hscale : Q * (if τ < T then 1 else 0) ≤ 1 ^ T) :
    Q * actualZeroServiceNumerator hψ hwidth hle ring C i T ≤ 1 ^ T := by
  exact Nat.le_trans
    (Nat.mul_le_mul_left Q
      (ring1_alias_badMass_le
        (κ := κ) (τ := τ) hψ hwidth hle ring C i T hfresh))
    hscale


#print axioms BirthShortDoneFixedSiteLoadBound.actual_fixed_site_scaled
#print axioms BirthShortDoneFixedSiteLoadBound.actual_fixed_site_exposure_crossmul
#print axioms BirthShortDoneFixedSiteLoadBound.listed_actual_le_overload
#print axioms BirthShortDoneFixedSiteLoadBound.listed_actual_exposure_crossmul
#print axioms BirthShortDoneFixedSiteLoadBound.actual_tau_zero_exposure_crossmul
#print axioms BirthShortDoneFixedSiteLoadBound.ring1_alias_exposure_crossmul


end BirthShortDoneFixedSiteLoadBound
