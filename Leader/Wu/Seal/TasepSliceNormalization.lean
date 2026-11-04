import Leader.Wu.Seal.HomeFrontQuotient

/-!
# First finite-slice brick for the seal-sweep TASEP argument

Before any spectral or Dirichlet-form estimate can be used, the stationary
event in the fixed-front slice needs an exact integer normalization.  This
module supplies that normalization without `Finset`, `Mathlib`, division, or
probability assumptions.

`frontSliceCard n k` is Pascal's triangle, hence the cardinality of the
binary `n`-site words with exactly `k` fronts.  The marked adjacent-front
event fixes two distinct sites to `true`, so its numerator is exactly
`frontSliceCard (n - 2) (k - 2)`.  The main theorem proves the division-free
identity

`n * (n - 1) * marked = k * (k - 1) * total`

and its scheduler-ready consequence `total <= n^2 * marked` for
`3 <= n` and `2 <= k < n`.  The concrete enumeration theorem below fixes the
first two list coordinates, so it gives that canonical marked pair mass at
least `1 / n^2`.  It does not identify an arbitrary cyclic `Fin n` edge with
those coordinates.  The remaining load-bearing steps are a genuine cyclic
rotation bridge and the proof that the directed ring TASEP is close enough to
the uniform fixed-slice law after `16 * n^4` edge choices.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepTasepMixingFirstBrickSol

set_option autoImplicit false

/-! ## A dependency-free fixed-front slice cardinality -/

/-- Number of binary words of length `n` with exactly `k` true entries.

The definition is Pascal's recursion.  It is deliberately integer-valued:
the later scheduler theorem compares favorable and total outcome counts and
never needs to divide inside Lean. -/
def frontSliceCard : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => frontSliceCard n k + frontSliceCard n (k + 1)

/-- Fixing two distinct marked sites to carry fronts removes those sites and
those two fronts.  This is the exact stationary numerator. -/
def markedPairSliceCard (n k : Nat) : Nat :=
  frontSliceCard (n - 2) (k - 2)

@[simp] theorem frontSliceCard_zero_zero : frontSliceCard 0 0 = 1 := rfl

@[simp] theorem frontSliceCard_zero_succ (k : Nat) :
    frontSliceCard 0 (k + 1) = 0 := rfl

@[simp] theorem frontSliceCard_succ_zero (n : Nat) :
    frontSliceCard (n + 1) 0 = 1 := rfl

@[simp] theorem frontSliceCard_any_zero (n : Nat) :
    frontSliceCard n 0 = 1 := by
  cases n <;> rfl

@[simp] theorem frontSliceCard_succ_succ (n k : Nat) :
    frontSliceCard (n + 1) (k + 1) =
      frontSliceCard n k + frontSliceCard n (k + 1) := rfl

/-- There are no fixed-slice words above the diagonal `k = n`. -/
theorem frontSliceCard_eq_zero_of_lt (n k : Nat) (h : n < k) :
    frontSliceCard n k = 0 := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => omega
      | succ k => rfl
  | succ n ih =>
      cases k with
      | zero => omega
      | succ k =>
          rw [frontSliceCard_succ_succ]
          rw [ih k (by omega), ih (k + 1) (by omega)]

/-- The all-front word is the unique word on the diagonal. -/
@[simp] theorem frontSliceCard_diag (n : Nat) :
    frontSliceCard n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [frontSliceCard_succ_succ, ih]
      rw [frontSliceCard_eq_zero_of_lt n (n + 1) (by omega)]

/-- Exactly `n` words of length `n` carry one front. -/
@[simp] theorem frontSliceCard_one (n : Nat) :
    frontSliceCard n 1 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [frontSliceCard_succ_succ, frontSliceCard_any_zero, ih]
      omega

/-! ## An explicit finite state-space enumeration -/

/-- All binary words of length `n`, with multiplicity one.  Prefixing is used
because it makes deleting two marked coordinates definitionally transparent. -/
def allFrontWords : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
      (allFrontWords n).flatMap (fun w => [false :: w, true :: w])

private theorem sum_map_two {α : Type} (xs : List α) :
    (xs.map fun _ => 2).sum = xs.length * 2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih, Nat.succ_mul]
      exact Nat.add_comm _ _

/-- The Boolean state enumeration has the expected `2^n` entries. -/
theorem allFrontWords_length (n : Nat) :
    (allFrontWords n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [allFrontWords, List.length_flatMap]
      rw [show
        (allFrontWords n).map
            (fun w => [false :: w, true :: w].length) =
          (allFrontWords n).map (fun _ => 2) by rfl]
      rw [sum_map_two, ih, Nat.pow_succ]

/-- Every enumerated Boolean word has exactly the advertised length. -/
theorem allFrontWords_word_length (n : Nat) :
    ∀ w ∈ allFrontWords n, w.length = n := by
  induction n with
  | zero =>
      intro w hw
      simp [allFrontWords] at hw
      subst w
      rfl
  | succ n ih =>
      intro w hw
      simp only [allFrontWords, List.mem_flatMap] at hw
      obtain ⟨tail, htail, hw⟩ := hw
      simp at hw
      rcases hw with rfl | rfl <;> simp [ih tail htail]

/-- Conversely, every Boolean word of length `n` occurs in the enumeration. -/
theorem mem_allFrontWords_of_length (n : Nat) (w : List Bool)
    (hlen : w.length = n) : w ∈ allFrontWords n := by
  induction n generalizing w with
  | zero =>
      have hw : w = [] := List.eq_nil_of_length_eq_zero hlen
      subst w
      simp [allFrontWords]
  | succ n ih =>
      cases w with
      | nil => simp at hlen
      | cons b tail =>
          have htail : tail.length = n := by simp at hlen; omega
          simp only [allFrontWords, List.mem_flatMap]
          refine ⟨tail, ih tail htail, ?_⟩
          cases b <;> simp

private theorem nodup_flatMap_of_nodup
    {A B : Type} (xs : List A) (f : A → List B)
    (hxs : xs.Nodup)
    (hfn : ∀ x, x ∈ xs → (f x).Nodup)
    (hdisjoint : ∀ x, x ∈ xs → ∀ y, y ∈ xs → x ≠ y →
      ∀ a, a ∈ f x → ∀ b, b ∈ f y → a ≠ b) :
    (xs.flatMap f).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hxs
      simp only [List.flatMap_cons]
      rw [List.nodup_append]
      refine ⟨hfn x (by simp), ?_, ?_⟩
      · apply ih hxs.2
        · intro y hy
          exact hfn y (by simp [hy])
        · intro y hy z hz hyz
          exact hdisjoint y (by simp [hy]) z (by simp [hz]) hyz
      · intro a ha b hb
        rw [List.mem_flatMap] at hb
        obtain ⟨y, hy, hby⟩ := hb
        apply hdisjoint x (by simp) y (by simp [hy])
        · intro hxy
          exact hxs.1 (hxy ▸ hy)
        · exact ha
        · exact hby

/-- No Boolean word is duplicated, so filtered list lengths are genuine
state-space cardinalities rather than multiplicity-weighted upper bounds. -/
theorem allFrontWords_nodup (n : Nat) : (allFrontWords n).Nodup := by
  induction n with
  | zero => simp [allFrontWords]
  | succ n ih =>
      rw [allFrontWords]
      apply nodup_flatMap_of_nodup _ _ ih
      · intro w hw
        simp
      · intro w hw v hv hne a ha b hb hab
        simp at ha hb
        rcases ha with rfl | rfl <;>
          rcases hb with rfl | rfl <;> simp_all

/-- Number of fronts in one binary word. -/
def frontWordMass : List Bool → Nat
  | [] => 0
  | b :: w => (if b then 1 else 0) + frontWordMass w

/-- The concrete finite state-space cardinality, computed by filtering the
explicit enumeration rather than by appealing to a typeclass cardinality. -/
def frontSliceWordCount (n k : Nat) : Nat :=
  (allFrontWords n).countP (fun w => decide (frontWordMass w = k))

private theorem count_mass_zero_extend (ws : List (List Bool)) :
    (ws.flatMap (fun w => [false :: w, true :: w])).countP
        (fun w => decide (frontWordMass w = 0)) =
      ws.countP (fun w => decide (frontWordMass w = 0)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.flatMap_cons, List.countP_append, List.countP_cons,
        List.countP_nil, frontWordMass]
      simp [ih, Nat.add_comm]

private theorem count_mass_succ_extend
    (ws : List (List Bool)) (k : Nat) :
    (ws.flatMap (fun w => [false :: w, true :: w])).countP
        (fun w => decide (frontWordMass w = k + 1)) =
      ws.countP (fun w => decide (frontWordMass w = k)) +
        ws.countP (fun w => decide (frontWordMass w = k + 1)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.flatMap_cons, List.countP_append, List.countP_cons,
        List.countP_nil, frontWordMass]
      by_cases hk : frontWordMass w = k
      · by_cases hks : frontWordMass w = k + 1
        · omega
        · simp [hk, ih, Nat.add_comm, Nat.add_assoc]
      · by_cases hks : frontWordMass w = k + 1
        · simp [hks, ih, Nat.add_comm, Nat.add_left_comm]
        · have hne : 1 + frontWordMass w ≠ k + 1 := by omega
          simp [hk, hks, hne, ih]

/-- The explicit list enumeration realizes Pascal's fixed-slice cardinality
exactly.  This is the state-space side of the stationary normalization. -/
theorem frontSliceWordCount_eq_card (n k : Nat) :
    frontSliceWordCount n k = frontSliceCard n k := by
  induction n generalizing k with
  | zero =>
      cases k <;> rfl
  | succ n ih =>
      cases k with
      | zero =>
          unfold frontSliceWordCount
          rw [allFrontWords, count_mass_zero_extend]
          change frontSliceWordCount n 0 = frontSliceCard (n + 1) 0
          rw [ih]
          simp
      | succ k =>
          unfold frontSliceWordCount
          rw [allFrontWords, count_mass_succ_extend]
          change
            frontSliceWordCount n k + frontSliceWordCount n (k + 1) =
              frontSliceCard (n + 1) (k + 1)
          rw [ih, ih, frontSliceCard_succ_succ]

/-- Concrete numerator for the event that the first two (distinct) marked
sites both carry fronts. -/
def markedPairWordCount (n k : Nat) : Nat :=
  (allFrontWords n).countP (fun w =>
    decide (frontWordMass w = k) &&
      match w with
      | true :: true :: _ => true
      | _ => false)

private theorem count_marked_extend_twice
    (ws : List (List Bool)) (k : Nat) :
    ((ws.flatMap (fun w => [false :: w, true :: w])).flatMap
        (fun w => [false :: w, true :: w])).countP
        (fun w =>
          decide (frontWordMass w = k + 2) &&
            match w with
            | true :: true :: _ => true
            | _ => false) =
      ws.countP (fun w => decide (frontWordMass w = k)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.flatMap_cons, List.flatMap_append, List.countP_append,
        List.countP_cons, List.countP_nil, frontWordMass]
      by_cases hk : frontWordMass w = k
      · simp [hk, ih, Nat.add_comm, Nat.add_left_comm]
      · have hne : 1 + (1 + frontWordMass w) ≠ k + 2 := by omega
        simp [hk, hne, ih]

/-- Exact fixed-slice marked-pair count in the explicit state enumeration. -/
theorem markedPairWordCount_eq_smaller_slice (m k : Nat) :
    markedPairWordCount (m + 2) (k + 2) = frontSliceWordCount m k := by
  unfold markedPairWordCount frontSliceWordCount
  rw [show m + 2 = (m + 1) + 1 by omega]
  rw [allFrontWords, allFrontWords]
  exact count_marked_extend_twice (allFrontWords m) k

/-- The concrete marked-pair numerator is precisely the smaller Pascal
slice.  This theorem is the bridge consumed by the normalized bound below. -/
theorem markedPairWordCount_eq_markedPairSliceCard
    (n k : Nat) (hn : 2 ≤ n) (hk : 2 ≤ k) :
    markedPairWordCount n k = markedPairSliceCard n k := by
  have hnrep : n = (n - 2) + 2 := by omega
  have hkrep : k = (k - 2) + 2 := by omega
  rw [hnrep, hkrep, markedPairWordCount_eq_smaller_slice,
    frontSliceWordCount_eq_card]
  simp [markedPairSliceCard]

/-! ## Exact incidence normalization -/

/-- Count incidences `(word, distinguished front)` in two ways.

The left side first chooses a `k`-front word and then one of its `k` fronts.
The right side first chooses the distinguished site and then a `(k-1)`-front
word on the other `n-1` sites.  This is the division-free identity behind the
usual binomial formula `k * C(n,k) = n * C(n-1,k-1)`. -/
theorem frontSliceCard_one_point_incidence
    (n k : Nat) (hk : 1 ≤ k) (hkn : k ≤ n) :
    k * frontSliceCard n k =
      n * frontSliceCard (n - 1) (k - 1) := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
      cases k with
      | zero => omega
      | succ k =>
          cases k with
          | zero =>
              simp [frontSliceCard_any_zero, Nat.add_comm]
          | succ j =>
              by_cases htop : j + 2 = n + 1
              · have hprev : j + 1 = n := by omega
                simp only [Nat.succ_sub_one]
                calc
                  (j + 2) * frontSliceCard (n + 1) (j + 2) =
                      (n + 1) * frontSliceCard (n + 1) (n + 1) := by
                        rw [htop]
                  _ = (n + 1) * frontSliceCard n n := by
                        rw [frontSliceCard_diag (n + 1),
                          frontSliceCard_diag n]
                  _ = (n + 1) * frontSliceCard n (j + 1) := by
                        rw [hprev]
              · have hinside : j + 2 ≤ n := by omega
                have hleft := ih (j + 1) (by omega) (by omega)
                have hright := ih (j + 2) (by omega) hinside
                cases n with
                | zero => omega
                | succ q =>
                    simp only [Nat.succ_sub_one] at hleft hright ⊢
                    rw [frontSliceCard_succ_succ]
                    let A := frontSliceCard (q + 1) (j + 1)
                    let B := frontSliceCard (q + 1) (j + 2)
                    let C := frontSliceCard q j
                    let D := frontSliceCard q (j + 1)
                    have hcoef (x : Nat) :
                        (j + 2) * x = (j + 1) * x + x := by
                      rw [show j + 2 = (j + 1) + 1 by omega,
                        Nat.add_mul, Nat.one_mul]
                    change (j + 2) * (A + B) = (q + 2) * A
                    change (j + 1) * A = (q + 1) * C at hleft
                    change (j + 2) * B = (q + 1) * D at hright
                    calc
                      (j + 2) * (A + B) =
                          (j + 2) * A + (j + 2) * B := Nat.mul_add _ _ _
                      _ = ((j + 1) * A + A) + (j + 2) * B := by
                            rw [hcoef A]
                      _ = ((q + 1) * C + A) + (q + 1) * D := by
                            rw [hleft, hright]
                      _ = (q + 1) * (C + D) + A := by
                            rw [Nat.mul_add]
                            ac_rfl
                      _ = (q + 1) * A + A := by
                            change
                              (q + 1) *
                                  (frontSliceCard q j +
                                    frontSliceCard q (j + 1)) + A = _
                            rw [← frontSliceCard_succ_succ q j]
                      _ = (q + 2) * A := by
                            simpa [show q + 2 = (q + 1) + 1 by omega,
                              Nat.one_mul] using
                              (Nat.add_mul (q + 1) 1 A).symm

/-- Count ordered incidences consisting of a fixed-slice word and two
distinct distinguished fronts.  No division or rational coercion is used. -/
theorem frontSliceCard_markedPair_exact
    (n k : Nat) (hk : 2 ≤ k) (hkn : k ≤ n) :
    n * (n - 1) * markedPairSliceCard n k =
      k * (k - 1) * frontSliceCard n k := by
  have hone := frontSliceCard_one_point_incidence n k (by omega) hkn
  have htwo := frontSliceCard_one_point_incidence
    (n - 1) (k - 1) (by omega) (by omega)
  unfold markedPairSliceCard
  grind

/-- Integer form of the marked-pair stationary lower bound.

For the nondegenerate TASEP slice (`3 <= n`, `2 <= k < n`), at least a
`1 / n^2` fraction of all slice configurations have fronts on the two marked
adjacent sites.  Written this way, the theorem plugs directly into the
project's exact `List.countP` scheduler numerators. -/
theorem frontSliceCard_le_square_mul_markedPair
    (n k : Nat) (hn : 3 ≤ n) (hk : 2 ≤ k) (hkn : k < n) :
    frontSliceCard n k ≤ n ^ 2 * markedPairSliceCard n k := by
  have hexact := frontSliceCard_markedPair_exact n k hk (by omega)
  have hkpos : 0 < k * (k - 1) :=
    Nat.mul_pos (by omega) (by omega)
  have hscale :
      frontSliceCard n k ≤
        (k * (k - 1)) * frontSliceCard n k := by
    simpa using Nat.mul_le_mul_right (frontSliceCard n k) hkpos
  have hcoeff : n * (n - 1) ≤ n ^ 2 := by
    have hsub : n - 1 ≤ n := Nat.le_of_lt (by omega)
    rw [Nat.pow_two]
    exact Nat.mul_le_mul_left n hsub
  calc
    frontSliceCard n k
        ≤ (k * (k - 1)) * frontSliceCard n k := hscale
    _ = n * (n - 1) * markedPairSliceCard n k := hexact.symm
    _ ≤ n ^ 2 * markedPairSliceCard n k :=
      Nat.mul_le_mul_right _ hcoeff

/-- Scheduler-ready concrete form for the canonical first two list
coordinates: in the explicit list of every binary `n`-site configuration,
the fixed-`k` slice count is at most `n^2` times the count with coordinates
zero and one occupied.  This is the exact integer normalization required
after an `L2`/total-variation mixing estimate.  Transport to an arbitrary
cyclic edge is intentionally not claimed here. -/
theorem frontSliceWordCount_le_square_mul_markedPairWordCount
    (n k : Nat) (hn : 3 ≤ n) (hk : 2 ≤ k) (hkn : k < n) :
    frontSliceWordCount n k ≤ n ^ 2 * markedPairWordCount n k := by
  rw [frontSliceWordCount_eq_card,
    markedPairWordCount_eq_markedPairSliceCard n k (by omega) hk]
  exact frontSliceCard_le_square_mul_markedPair n k hn hk hkn

/-! ## Kernel dependency audit

These capstones expose the dependencies of the exhaustive enumeration, exact
integer normalization, and scheduler-ready lower bound to Lean's kernel.
-/

#print axioms allFrontWords_nodup
#print axioms frontSliceCard_markedPair_exact
#print axioms frontSliceWordCount_le_square_mul_markedPairWordCount

end PPartialSealSweepTasepMixingFirstBrickSol
end PPLLCompleteMultiLeaderCleanup
