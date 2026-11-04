import Leader.Wu.Birth.ShortDoneParticipationLoadMass

namespace BirthShortDoneParticipationLoadBound

open PPLL PPLLResearchFormulation
open BirthShortDoneParticipationLoadMass

set_option autoImplicit false
set_option pp.structureInstances false

variable {n T m τ Q : Nat}

@[simp] theorem factorialMomentCap_order_zero (n T : Nat) :
    factorialMomentCap n T 0 = n ^ T := by
  cases T <;> rfl

@[simp] theorem factorialMomentCap_horizon_zero_succ (n m : Nat) :
    factorialMomentCap n 0 (m + 1) = 0 := rfl

/-- Above the horizon there are not enough charged letters to form an
m-subset.  This is proved only from the defining recurrence. -/
theorem factorialMomentCap_zero_of_lt (n T m : Nat) (h : T < m) :
    factorialMomentCap n T m = 0 := by
  induction T generalizing m with
  | zero =>
      cases m with
      | zero => omega
      | succ m => rfl
  | succ T ih =>
      cases m with
      | zero => omega
      | succ j =>
          rw [factorialMomentCap]
          have h1 : factorialMomentCap n T (j + 1) = 0 := by
            exact ih (j + 1) (by omega)
          have h0 : factorialMomentCap n T j = 0 := by
            exact ih j (by omega)
          rw [h1, h0]
          simp

/-- Exact closed form with all division cleared.  For n>0 this is equivalent
to C(T,m) * 2^m * n^(T-m), but the statement has no subtraction/division and
also handles m>T and zero boundaries literally. -/
theorem factorialMomentCap_crossmul_exact (n T m : Nat) :
    n ^ m * factorialMomentCap n T m =
      n ^ T * (chooseCount T m * 2 ^ m) := by
  induction T generalizing m with
  | zero =>
      cases m <;> simp [factorialMomentCap, chooseCount]
  | succ T ih =>
      cases m with
      | zero => simp [factorialMomentCap, chooseCount]
      | succ j =>
          rw [factorialMomentCap, Nat.mul_add]
          have h1 := ih (Nat.succ j)
          have h0 := ih j
          calc
            n ^ (Nat.succ j) *
                  (n * factorialMomentCap n T (Nat.succ j)) +
                n ^ (Nat.succ j) *
                  (2 * factorialMomentCap n T j) =
              n * (n ^ (Nat.succ j) *
                factorialMomentCap n T (Nat.succ j)) +
                (2 * n) * (n ^ j * factorialMomentCap n T j) := by
                  simp only [Nat.pow_succ]
                  ac_rfl
            _ = n * (n ^ T *
                  (chooseCount T (Nat.succ j) * 2 ^ (Nat.succ j))) +
                (2 * n) * (n ^ T * (chooseCount T j * 2 ^ j)) := by
                  rw [h1, h0]
            _ = n ^ (Nat.succ T) *
                  (chooseCount (Nat.succ T) (Nat.succ j) *
                    2 ^ (Nat.succ j)) := by
                  simp only [chooseCount, Nat.pow_succ]
                  rw [Nat.add_mul, Nat.mul_add]
                  ac_rfl

/-- Direct fixed-node consequence of the source factorial-moment domination. -/
theorem fixed_node_scaled (hn2 : 2 ≤ n) (ring : DirectedRing n)
    (i : Fin n) (T m : Nat) :
    n ^ m * overloadNumerator ring i T m ≤
      n ^ T * (chooseCount T m * 2 ^ m) := by
  calc
    n ^ m * overloadNumerator ring i T m ≤
        n ^ m * factorialMomentCap n T m :=
      Nat.mul_le_mul_left _ (fixed_node_overload_bound hn2 ring i T m)
    _ = n ^ T * (chooseCount T m * 2 ^ m) :=
      factorialMomentCap_crossmul_exact n T m

/-- Multiplicity union charge for one caller-specified finite site list.
No factor n is inserted.  If sites is Nodup, sites.length is the actual set
cardinality; duplicates merely give a conservative repeated charge. -/
def listedSiteOverloadMass (ring : DirectedRing n) (sites : List (Fin n))
    (T m : Nat) : Nat :=
  (sites.map (fun i => overloadNumerator ring i T m)).sum

theorem listedSiteOverloadMass_le_cap (hn2 : 2 ≤ n)
    (ring : DirectedRing n) (sites : List (Fin n)) (T m : Nat) :
    listedSiteOverloadMass ring sites T m ≤
      sites.length * factorialMomentCap n T m := by
  unfold listedSiteOverloadMass
  induction sites with
  | nil => simp
  | cons i sites ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hi := fixed_node_overload_bound hn2 ring i T m
      calc
        overloadNumerator ring i T m +
              (sites.map (fun j => overloadNumerator ring j T m)).sum ≤
            factorialMomentCap n T m +
              sites.length * factorialMomentCap n T m :=
          Nat.add_le_add hi ih
        _ = Nat.succ sites.length * factorialMomentCap n T m := by
          rw [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- The same exact closed form after union-charging only the named sites. -/
theorem listedSiteOverloadMass_scaled (hn2 : 2 ≤ n)
    (ring : DirectedRing n) (sites : List (Fin n)) (T m : Nat) :
    n ^ m * listedSiteOverloadMass ring sites T m ≤
      n ^ T * (sites.length * (chooseCount T m * 2 ^ m)) := by
  have hl := listedSiteOverloadMass_le_cap hn2 ring sites T m
  have hc := factorialMomentCap_crossmul_exact n T m
  calc
    n ^ m * listedSiteOverloadMass ring sites T m ≤
        n ^ m * (sites.length * factorialMomentCap n T m) :=
      Nat.mul_le_mul_left _ hl
    _ = sites.length * (n ^ m * factorialMomentCap n T m) := by
      ac_rfl
    _ = sites.length * (n ^ T * (chooseCount T m * 2 ^ m)) := by
      rw [hc]
    _ = n ^ T * (sites.length * (chooseCount T m * 2 ^ m)) := by
      ac_rfl

/-- Fixed-list finite union bound, entirely cross-multiplied.  The hypothesis
is the arithmetic check needed for failure fraction at most 1/Q. -/
theorem listed_sites_exposure_crossmul (hn2 : 2 ≤ n)
    (ring : DirectedRing n) (sites : List (Fin n)) (T m Q : Nat)
    (hscale :
      Q * sites.length * (chooseCount T m * 2 ^ m) ≤ n ^ m) :
    Q * listedSiteOverloadMass ring sites T m ≤ n ^ T := by
  have hs := listedSiteOverloadMass_scaled hn2 ring sites T m
  have hQ := Nat.mul_le_mul_left Q hs
  have hr := Nat.mul_le_mul_left (n ^ T) hscale
  have hboth :
      n ^ m * (Q * listedSiteOverloadMass ring sites T m) ≤
        n ^ m * n ^ T := by
    calc
      n ^ m * (Q * listedSiteOverloadMass ring sites T m) =
          Q * (n ^ m * listedSiteOverloadMass ring sites T m) := by
        ac_rfl
      _ ≤ Q * (n ^ T *
            (sites.length * (chooseCount T m * 2 ^ m))) := hQ
      _ = n ^ T *
            (Q * sites.length * (chooseCount T m * 2 ^ m)) := by
        ac_rfl
      _ ≤ n ^ T * n ^ m := hr
      _ = n ^ m * n ^ T := Nat.mul_comm _ _
  have hn : 0 < n := by omega
  exact Nat.le_of_mul_le_mul_left hboth (Nat.pow_pos hn)

/-- Singleton specialization: no hidden all-sites factor. -/
theorem fixed_node_exposure_crossmul (hn2 : 2 ≤ n)
    (ring : DirectedRing n) (i : Fin n) (T m Q : Nat)
    (hscale : Q * (chooseCount T m * 2 ^ m) ≤ n ^ m) :
    Q * overloadNumerator ring i T m ≤ n ^ T := by
  have hs :
      Q * ([i] : List (Fin n)).length *
          (chooseCount T m * 2 ^ m) ≤ n ^ m := by
    simpa using hscale
  have h := listed_sites_exposure_crossmul hn2 ring
    ([i] : List (Fin n)) T m Q hs
  simpa [listedSiteOverloadMass] using h

/-- The alias case must not use the two-letter cap.  Every listed Fin 1 site
has the deterministic source count, so this is exact even with duplicates. -/
theorem ring1_listedSiteOverloadMass_exact
    (ring : DirectedRing 1) (sites : List (Fin 1)) (T m : Nat) :
    listedSiteOverloadMass ring sites T m =
      sites.length * (if m ≤ T then 1 else 0) := by
  unfold listedSiteOverloadMass
  induction sites with
  | nil => simp
  | cons i sites ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ring1_overload_exact ring i T m, ih, Nat.succ_mul]
      exact Nat.add_comm _ _

#print axioms BirthShortDoneParticipationLoadBound.factorialMomentCap_zero_of_lt
#print axioms BirthShortDoneParticipationLoadBound.factorialMomentCap_crossmul_exact
#print axioms BirthShortDoneParticipationLoadBound.fixed_node_scaled
#print axioms BirthShortDoneParticipationLoadBound.listedSiteOverloadMass_le_cap
#print axioms BirthShortDoneParticipationLoadBound.listed_sites_exposure_crossmul
#print axioms BirthShortDoneParticipationLoadBound.ring1_listedSiteOverloadMass_exact

end BirthShortDoneParticipationLoadBound
