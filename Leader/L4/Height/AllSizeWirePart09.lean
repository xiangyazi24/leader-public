import Leader.L4.Height.AllSizeWirePart08
set_option Elab.async false

namespace L4.Height.AllSizeWire
open AllSizeSpine L4.Compiler.Native Classical

section ProductionSize

open PhysicalCustody AllSizeProtocol BStarH6WordChart BStarH6Ordinal

/-- The exact advice implies the lower endpoint of its packed size band. -/
theorem packed_band_min_of_advice {s n : Nat} (hs : 6 ≤ s) (ha : s = ell (ell n)) :
    packedBandMin s ≤ n := by
  have hOuter : ¬ ell (ell n) ≤ s - 1 := by
    rw [← ha]
    omega
  have hInner : ¬ ell n ≤ 2 ^ (s - 1) :=
    fun h => hOuter ((ell_le_iff (ell n) (s - 1)).2 h)
  have hSize : ¬ n ≤ 2 ^ (2 ^ (s - 1)) :=
    fun h => hInner ((ell_le_iff n (2 ^ (s - 1))).2 h)
  exact Nat.succ_le_of_lt (Nat.lt_of_not_ge hSize)

theorem three_word_width_lt_band (s : Nat) (hs : 6 ≤ s) :
    3 * 1024 * 2 ^ s < packedBandMin s := by
  have hBands : ∀ t : Nat, 3 * 1024 * 2 ^ (6 + t) < packedBandMin (6 + t) := by
    intro t
    induction t with
    | zero => decide
    | succ t ih =>
      have hGrowth := packed_band_min_growth (6 + t) (by omega)
      change 3 * 1024 * 2 ^ ((6 + t) + 1) < packedBandMin ((6 + t) + 1)
      calc
        3 * 1024 * 2 ^ ((6 + t) + 1) = 2 * (3 * 1024 * 2 ^ (6 + t)) := by
          rw [Nat.pow_succ]
          ac_rfl
        _ < 2 * packedBandMin (6 + t) := Nat.mul_lt_mul_of_pos_left ih (by decide)
        _ ≤ 2048 * packedBandMin (6 + t) := Nat.mul_le_mul_right _ (by decide)
        _ ≤ packedBandMin ((6 + t) + 1) := hGrowth
  have hIndex : 6 + (s - 6) = s := by omega
  simpa only [hIndex] using hBands (s - 6)

/-- Every packed production circumference exceeds three maximal word
widths. -/
theorem packed_production_room {s n : Nat} (hs : 6 ≤ s) (ha : s = ell (ell n)) :
    3 * 1024 * radWidth s < n := by
  have hWidth : radWidth s ≤ 2^s := Nat.sub_le _ _
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ hWidth)
    (Nat.lt_of_lt_of_le (three_word_width_lt_band s hs) (packed_band_min_of_advice hs ha))

/-- Traverse once around the raw ring. Every incoming header seam
charges its preceding word width, and the original ordinal cancels
after one revolution. -/
theorem circumference_le_header_capacity {n : Nat}
    (h : Fin n → Bool) (hh : ∃ i, h i = true) (W : Nat)
    (upper : ∀ e, h (rightNeighbor e) = true → ordinal h hh e + 1 ≤ W) :
    n ≤ total h * W := by
  have hn : 0 < n := by
    obtain ⟨i, _⟩ := hh
    exact Nat.zero_lt_of_lt i.isLt
  let siteAt (k : Nat) : Fin n := ⟨k % n, Nat.mod_lt _ hn⟩
  let before (k : Nat) : Fin n := RearTrace.predecessor (siteAt k)
  have hNext (k : Nat) : rightNeighbor (siteAt k) = siteAt (k+1) := by
    apply Fin.ext
    change (k % n + 1) % n = (k+1) % n
    rw [Nat.mod_add_mod]
  have hBefore (k : Nat) : before (k+1) = siteAt k :=
    (congrArg RearTrace.predecessor (hNext k)).symm.trans
      (RearTrace.predecessor_right (siteAt k))
  have hWrap : siteAt n = siteAt 0 := by
    apply Fin.ext
    change n % n = 0 % n
    rw [Nat.mod_self, Nat.zero_mod]
  have hScan (k : Nat) (hk : k ≤ n) :
      k + ordinal h hh (before 0) ≤ W * countPrefix h k + ordinal h hh (before k) := by
    induction k with
    | zero => simp [countPrefix]
    | succ k ih =>
      have hBelow : k < n := by omega
      have hIndex : (siteAt k).val = k := Nat.mod_eq_of_lt hBelow
      have hPrefix := prefix_succ h (siteAt k)
      rw [hIndex] at hPrefix
      have hNeighbor : rightNeighbor (before k) = siteAt k :=
        RearTrace.right_predecessor (siteAt k)
      have hOrdinal := ordinal_right h hh (before k)
      rw [hNeighbor] at hOrdinal
      have hAfter := (congrArg (ordinal h hh) (hBefore k)).trans hOrdinal
      have hPrevious := ih (Nat.le_of_lt hBelow)
      rw [hPrefix, hAfter]
      cases hi : h (siteAt k)
      · simp [hi]
        omega
      · have hSeam : h (rightNeighbor (before k)) = true := hNeighbor.symm ▸ hi
        have hWidth := upper (before k) hSeam
        simp [hi, Nat.mul_add]
        omega
  have hClosed : before n = before 0 := congrArg RearTrace.predecessor hWrap
  have hFull := hScan n (Nat.le_refl n)
  rw [hClosed] at hFull
  have hBound : n ≤ W * total h := by
    change n + ordinal h hh (before 0) ≤ W * total h + ordinal h hh (before 0) at hFull
    omega
  simpa only [Nat.mul_comm W (total h)] using hBound

/-- The witness's actual incoming seams partition the circumference
into words of width at most the production cap. -/
theorem packed_header_capacity {s n : Nat} {x : Raw s n} (g : CustodyWitness x) :
    n ≤ headers g * (1024 * radWidth s) :=
  circumference_le_header_capacity (oldH6 (rows s) g.base) g.hh
    (1024 * radWidth s) g.upperWidth

/-- The actual custody layout has at least four owner words at production
advice, including the smallest packed size. -/
theorem packed_production_headers {s n : Nat} {x : Raw s n}
    (g : CustodyWitness x) (hs : 6 ≤ s) (ha : s = ell (ell n)) :
    4 ≤ headers g := by
  by_cases h : 4 ≤ headers g
  · exact h
  · have hFew : headers g ≤ 3 := by omega
    have hBound := Nat.le_trans (packed_header_capacity g)
      (Nat.mul_le_mul_right (1024 * radWidth s) hFew)
    have hRoom := packed_production_room hs ha
    have heq : 3 * (1024 * radWidth s) = 3 * 1024 * radWidth s :=
      (Nat.mul_assoc 3 1024 (radWidth s)).symm
    rw [heq] at hBound
    omega

/-- The scoped service premise is supplied by the actual production
advice and the physical custody partition. -/
theorem packed_service_production {s n : Nat} (_hn : 4 ≤ n) (hs : 6 ≤ s)
    (ha : s = AllSizeProtocol.ell (AllSizeProtocol.ell n))
    {x : PhysicalCustody.Raw s n} (g : PhysicalCustody.CustodyWitness x) :
    L4.Height.ProductionCustody.Production g :=
  ⟨ha, hs, packed_production_room hs ha, packed_production_headers g hs ha⟩

end ProductionSize

end L4.Height.AllSizeWire
