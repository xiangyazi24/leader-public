import Leader.Wu.Birth.ShortDoneTerminalFixedSite
import Leader.Wu.Birth.ShortDoneParticipationLoadBound

namespace BirthShortDoneTerminalLoadBound

open PPLL PPLLResearchFormulation
open BirthShortDoneParticipationBudget
open BirthShortDoneParticipationLoadMass
open BirthShortDoneParticipationLoadBound
open BirthShortDoneFixedSiteConsumer
open BirthShortDoneTerminalFixedSite
open FixedSpanRenewalPayload FiniteUniformStoppingTree

set_option autoImplicit false
set_option pp.structureInstances false

variable {n ψ width κ τ T Q : Nat}

/-- Exact bad-event numerator for the terminal-entry repaired host, over the
complete original `n^T` raw scheduler words. -/
def terminalZeroServiceNumerator
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → Local ψ κ τ)
    (i : Fin n) (T : Nat) : Nat :=
  wordSum n T (fun w =>
    fixedSiteZeroServiceBit ring
      (BirthShortDoneTerminalHost.row hψ hwidth hle) i C w)

/-- Sum the terminal host's pointwise bad-event domination over exactly the
same complete raw-word enumeration used by `overloadNumerator`. -/
theorem terminalZeroServiceNumerator_le_overload
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → Local ψ κ τ)
    (i : Fin n) (T : Nat) (hfresh : (C i).stall.val = τ) :
    terminalZeroServiceNumerator hψ hwidth hle ring C i T ≤
      overloadNumerator ring i T (τ + 1) := by
  unfold terminalZeroServiceNumerator overloadNumerator
  rw [<- rawWord_sum n T (fun w =>
      fixedSiteZeroServiceBit ring
        (BirthShortDoneTerminalHost.row hψ hwidth hle) i C w),
    <- rawWord_sum n T (overloadBit ring i (τ + 1))]
  apply ofFn_sum_le
  intro a
  exact terminal_zeroServiceBit_le_overload (κ := κ) (τ := τ)
    hψ hwidth hle ring C i (rawWord n T a) hfresh

/-- Fixed selected site.  The arithmetic premise is exactly the existing
cross-multiplied binomial/factorial bound at order `τ+1`. -/
theorem terminal_fixed_site_exposure_crossmul
    (hn2 : 2 ≤ n) (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (ring : DirectedRing n)
    (C : Fin n → Local ψ κ τ) (i : Fin n) (T Q : Nat)
    (hfresh : (C i).stall.val = τ)
    (hscale :
      Q * (chooseCount T (τ + 1) * 2 ^ (τ + 1)) ≤ n ^ (τ + 1)) :
    Q * terminalZeroServiceNumerator hψ hwidth hle ring C i T ≤ n ^ T := by
  calc
    Q * terminalZeroServiceNumerator hψ hwidth hle ring C i T ≤
        Q * overloadNumerator ring i T (τ + 1) :=
      Nat.mul_le_mul_left Q
        (terminalZeroServiceNumerator_le_overload
          (κ := κ) (τ := τ) hψ hwidth hle ring C i T hfresh)
    _ ≤ n ^ T :=
      fixed_node_exposure_crossmul hn2 ring i T (τ + 1) Q hscale

/-- Multiplicity union numerator for exactly the caller-listed physical sites.
Duplicates are a conservative repeated union charge. -/
def listedTerminalZeroServiceMass
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → Local ψ κ τ)
    (sites : List (Fin n)) (T : Nat) : Nat :=
  (sites.map (fun i =>
    terminalZeroServiceNumerator hψ hwidth hle ring C i T)).sum

/-- Only listed sites need fresh initial timer credit. -/
theorem listedTerminalZeroServiceMass_le_overload
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → Local ψ κ τ)
    (sites : List (Fin n)) (T : Nat)
    (hfresh : ∀ i, i ∈ sites → (C i).stall.val = τ) :
    listedTerminalZeroServiceMass hψ hwidth hle ring C sites T ≤
      listedSiteOverloadMass ring sites T (τ + 1) := by
  revert hfresh
  induction sites with
  | nil =>
      intro hfresh
      simp [listedTerminalZeroServiceMass, listedSiteOverloadMass]
  | cons i sites ih =>
      intro hfresh
      have hi : (C i).stall.val = τ := hfresh i (by simp)
      have htail : ∀ j, j ∈ sites → (C j).stall.val = τ := by
        intro j hj
        exact hfresh j (by simp [hj])
      have hhead := terminalZeroServiceNumerator_le_overload
        (κ := κ) (τ := τ) hψ hwidth hle ring C i T hi
      have hrest := ih htail
      simpa [listedTerminalZeroServiceMass, listedSiteOverloadMass] using
        Nat.add_le_add hhead hrest

/-- Finite listed-site union exposure.  The only multiplicity factor is the
literal `sites.length`; there is no automatic all-sites factor. -/
theorem listed_terminal_exposure_crossmul
    (hn2 : 2 ≤ n) (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (ring : DirectedRing n)
    (C : Fin n → Local ψ κ τ) (sites : List (Fin n)) (T Q : Nat)
    (hfresh : ∀ i, i ∈ sites → (C i).stall.val = τ)
    (hscale :
      Q * sites.length * (chooseCount T (τ + 1) * 2 ^ (τ + 1)) ≤
        n ^ (τ + 1)) :
    Q * listedTerminalZeroServiceMass hψ hwidth hle ring C sites T ≤
      n ^ T := by
  calc
    Q * listedTerminalZeroServiceMass hψ hwidth hle ring C sites T ≤
        Q * listedSiteOverloadMass ring sites T (τ + 1) :=
      Nat.mul_le_mul_left Q
        (listedTerminalZeroServiceMass_le_overload
          hψ hwidth hle ring C sites T hfresh)
    _ ≤ n ^ T :=
      listed_sites_exposure_crossmul hn2 ring sites T (τ + 1) Q hscale

/-- `τ=0`: freshness at the selected site is automatic because its stall is
`Fin 1`; the arithmetic condition is the literal order-one specialization. -/
theorem terminal_tau_zero_exposure_crossmul
    (hn2 : 2 ≤ n) (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (ring : DirectedRing n)
    (C : Fin n → Local ψ κ 0) (i : Fin n) (T Q : Nat)
    (hscale : Q * (chooseCount T 1 * 2) ≤ n) :
    Q * terminalZeroServiceNumerator hψ hwidth hle ring C i T ≤ n ^ T := by
  have hfresh : (C i).stall.val = 0 := by
    have hlt := (C i).stall.isLt
    omega
  calc
    Q * terminalZeroServiceNumerator hψ hwidth hle ring C i T ≤
        Q * overloadNumerator ring i T 1 :=
      Nat.mul_le_mul_left Q
        (terminalZeroServiceNumerator_le_overload
          (κ := κ) (τ := 0) hψ hwidth hle ring C i T hfresh)
    _ ≤ n ^ T := by
      apply fixed_node_exposure_crossmul hn2 ring i T 1 Q
      simpa using hscale

/-- `n=1` alias boundary: endpoint participation is one charge per raw edge,
so use the exact ring-one overload split rather than the two-letter cap. -/
theorem terminal_ring1_alias_exposure_crossmul
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing 1) (C : Fin 1 → Local ψ κ τ)
    (i : Fin 1) (T Q : Nat) (hfresh : (C i).stall.val = τ)
    (hscale : Q * (if τ < T then 1 else 0) ≤ 1 ^ T) :
    Q * terminalZeroServiceNumerator hψ hwidth hle ring C i T ≤ 1 ^ T := by
  calc
    Q * terminalZeroServiceNumerator hψ hwidth hle ring C i T ≤
        Q * overloadNumerator ring i T (τ + 1) :=
      Nat.mul_le_mul_left Q
        (terminalZeroServiceNumerator_le_overload
          (κ := κ) (τ := τ) hψ hwidth hle ring C i T hfresh)
    _ = Q * (if τ < T then 1 else 0) := by
      rw [ring1_tau_split ring i T τ]
    _ ≤ 1 ^ T := hscale

#print axioms BirthShortDoneTerminalLoadBound.terminalZeroServiceNumerator_le_overload
#print axioms BirthShortDoneTerminalLoadBound.terminal_fixed_site_exposure_crossmul
#print axioms BirthShortDoneTerminalLoadBound.listedTerminalZeroServiceMass_le_overload
#print axioms BirthShortDoneTerminalLoadBound.listed_terminal_exposure_crossmul
#print axioms BirthShortDoneTerminalLoadBound.terminal_tau_zero_exposure_crossmul
#print axioms BirthShortDoneTerminalLoadBound.terminal_ring1_alias_exposure_crossmul

end BirthShortDoneTerminalLoadBound
