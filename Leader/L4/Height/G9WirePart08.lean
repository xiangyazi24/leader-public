import Leader.L4.Height.G9WirePart07
set_option Elab.async false

namespace L4.Height.G9Wire
open G9Spine L4.Compiler.Native Classical

section PackedGeometry
open PhysicalCustody CustodySpec ClockServiceSpec AllSizeProtocol BStarH6WordChart

variable {s n : Nat}

theorem foldmax_le (xs : List Nat) (a bound : Nat) (ha : a ≤ bound)
    (hxs : ∀ v ∈ xs, v ≤ bound) : xs.foldl max a ≤ bound := by
  induction xs generalizing a with
  | nil => exact ha
  | cons v vs ih =>
    exact ih (max a v) (Nat.max_le.mpr ⟨ha, hxs v (by simp)⟩)
      (fun z hz => hxs z (by simp [hz]))

theorem le_foldmax (xs : List Nat) (a : Nat) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => exact Nat.le_refl _
  | cons v vs ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem member_le_foldmax (xs : List Nat) (a v : Nat) (hv : v ∈ xs) :
    v ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp at hv
  | cons h t ih =>
    rcases List.mem_cons.mp hv with rfl | ht
    · exact Nat.le_trans (Nat.le_max_right _ _) (le_foldmax _ _)
    · exact ih _ ht

theorem packed_width_bounds {x : Raw s n} (g : CustodyWitness x) :
    0 < maxWordWidth g ∧ maxWordWidth g ≤ 1024 * radWidth s := by
  let val := fun e : Fin n => if oldH6 (rows s) g.base (rightNeighbor e) then
    BStarH6Ordinal.oldOrdinal (rows s) g.base g.hh e + 1 else 0
  change 0 < (List.ofFn val).foldl max 0 ∧ (List.ofFn val).foldl max 0 ≤ _
  constructor
  · obtain ⟨i,hi⟩ := g.hh
    let e := RearTrace.predecessor i
    have he : rightNeighbor e = i := RearTrace.right_predecessor _
    have vpos : 0 < val e := by simp [val,he,hi]
    exact Nat.lt_of_lt_of_le vpos (member_le_foldmax _ _ _ (List.mem_ofFn.mpr ⟨e,rfl⟩))
  · apply foldmax_le _ _ _ (Nat.zero_le _)
    intro z hz
    obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hz
    by_cases h : oldH6 (rows s) g.base (rightNeighbor e) = true
    · simpa [val,h] using g.upperWidth e h
    · simp [val,h]

theorem packed_clock_modulus (hn : 4 ≤ n) (hs : 6 ≤ s)
    (ha : s = ell (ell n)) :
    let D := packedData s n hn hs
    Recover.StageTwo.ClockParams (modulus D.r) ∧
      ∀ j : D.Chart, D.m j < modulus D.r / 2 := by
  let D := packedData s n hn hs
  have hr : D.r = 2 ^ ceilingLogTwo (ceilingLogTwo n) - 1 :=
    congrArg (fun advice : Nat => 2 ^ advice - 1) ha
  exact packed_modulus_parameters D hn hr (fun j => j.2.packed)

/-- The fixed physical header count fits strictly inside one half-period. -/
theorem packed_header_count_lt_half (hn : 4 ≤ n) (hs : 6 ≤ s)
    (ha : s = ell (ell n)) :
    let D := packedData s n hn hs
    ∀ j : D.Chart, D.m j < modulus D.r / 2 :=
  (packed_clock_modulus hn hs ha).2

theorem packed_parameters_at_budget (hn : 4 ≤ n) (hs : 6 ≤ s)
    (ha : s = ell (ell n)) (budget : Nat) :
    let D := packedData s n hn hs
    ∀ j : D.Chart, Recover.StageTwo.ClockParams (modulus D.r) ∧
      D.m j / 2 < modulus D.r / 2 ∧ 0 < D.block j ∧
      4*(2^(5*budget+1)*D.block j) ≤ D.scale budget ∧ D.m j * D.r ≤ n := by
  let D := packedData s n hn hs
  have packing (j : D.Chart) : D.m j * D.r ≤ n := j.2.packed
  obtain ⟨hm, hd⟩ := packed_clock_modulus hn hs ha
  have hDiameter (j : D.Chart) : D.m j / 2 < modulus D.r / 2 := by
    have hCount : D.m j < modulus D.r / 2 := hd j
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hCount
  exact parameters_of_packing D (by omega) budget hm hDiameter
    (fun j => (packed_width_bounds j.2).1) (fun j => (packed_width_bounds j.2).2) packing

theorem packed_parameters (hn : 4 ≤ n) (hs : 6 ≤ s) (ha : s = ell (ell n)) :
    let D := packedData s n hn hs
    ∀ j : D.Chart, Recover.StageTwo.ClockParams (modulus D.r) ∧
      D.m j / 2 < modulus D.r / 2 ∧ 0 < D.block j ∧
      4*(2^(5*(2^32 : Nat)+1)*D.block j) ≤ D.scale (2^32) ∧ D.m j * D.r ≤ n :=
  packed_parameters_at_budget hn hs ha (2^32)

theorem custody_coeff_eq (g : Nat) : packingCoefficient g = custodyCoeff g := rfl

end PackedGeometry

theorem physical_reservation_margin {G level key : Nat} (hLevel : level ≤ G)
    (hKey : key ≤ level + 1) : key + 2 ≤ BStarPhysicalLiftAlignment.frontier G := by
  have h := (BStarPhysicalLiftAlignment.frontier_spec G).1
  omega

/-- The stronger strict warmup margin depends on which opening was chosen. -/
theorem reservation_frontiers_differ :
    30 + 2 < publicationFrontier 29 1 ∧
    30 + 2 = BStarPhysicalLiftAlignment.frontier 29 := by decide

end L4.Height.G9Wire
