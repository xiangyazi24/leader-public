import Leader.L3.Top.MarkedProgress

/-!
# Q7: the nominated edge off rank zero

Consumer: `Leader/L3/Top/MarkedDebtRows.lean` (the `progress` row of
`TopMarkedDebtRows`).
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- Scan flags after one more register.

Consumer: `rank_progress`. -/
theorem scanFlags_succ_right (cells : Nat → Cell) :
    ∀ k j ob vb,
      scanFlags cells (k + 1) j ob vb =
        (nob (scanFlags cells k j ob vb).1 (cells (j + k)),
          nvb (scanFlags cells k j ob vb).1 (scanFlags cells k j ob vb).2 (cells (j + k))) := by
  intro k
  induction k with
  | zero => intro j ob vb; simp [scanFlags]
  | succ k ih =>
      intro j ob vb
      have h1 : scanFlags cells (k + 1 + 1) j ob vb =
          scanFlags cells (k + 1) (j + 1) (nob ob (cells j)) (nvb ob vb (cells j)) := rfl
      have h2 : scanFlags cells (k + 1) j ob vb =
          scanFlags cells k (j + 1) (nob ob (cells j)) (nvb ob vb (cells j)) := rfl
      rw [h1, ih (j + 1), h2]
      have e : j + 1 + k = j + (k + 1) := by omega
      rw [e]

/-- A rightmost register with a property.

Consumer: `rank_progress`. -/
theorem exists_max (r : Nat) (P : Nat → Prop) (h : ∃ i, i < r ∧ P i) :
    ∃ i, i < r ∧ P i ∧ ∀ k, i < k → k < r → ¬ P k := by
  obtain ⟨i0, hi0, hP0⟩ := h
  have key : ∀ d i, r - i ≤ d → i < r → P i →
      ∃ i', i' < r ∧ P i' ∧ ∀ k, i' < k → k < r → ¬ P k := by
    intro d
    induction d with
    | zero => intro i hd hi; omega
    | succ d ih =>
        intro i hd hi hPi
        by_cases hex : ∃ k, i < k ∧ k < r ∧ P k
        · obtain ⟨k, hk1, hk2, hk3⟩ := hex
          exact ih k (by omega) hk2 hk3
        · exact ⟨i, hi, hPi, fun k hk1 hk2 hk3 => hex ⟨k, hk1, hk2, hk3⟩⟩
  exact key r i0 (by omega) hi0 hP0

/-- A clean register weighs nothing when no violator was seen.

Consumer: `rank_progress`. -/
theorem wt_zero_of_clean (r j : Nat) (ob : Bool) (c : Cell)
    (h1 : violC ob c = false) (h2 : c.c ≠ .inh) : wt r j ob false c = 0 := by
  rcases c with ⟨ci, cc⟩
  cases ci <;> cases cc <;> cases ob <;>
    simp (config := { decide := true }) [wt, gateW, violC] at h1 h2 ⊢

/-- Without violators and inherited carries the rank is zero.

Consumer: `rank_progress`. -/
theorem scan_zero_clean (r : Nat) (cells : Nat → Cell) :
    ∀ k j ob vb, vb = false →
      (∀ i, i < k → violC (scanFlags cells i j ob vb).1 (cells (j + i)) = false ∧
        (cells (j + i)).c ≠ .inh) →
      scan r cells k j ob vb = 0 := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
      intro j ob vb hvb h
      have h0 := h 0 (by omega)
      simp only [scanFlags, Nat.add_zero] at h0
      have hw : wt r j ob vb (cells j) = 0 := by
        rw [hvb]
        exact wt_zero_of_clean r j ob (cells j) h0.1 h0.2
      have hv' : nvb ob vb (cells j) = false := by
        simp [nvb, hvb, h0.1]
      simp only [scan, hw, Nat.zero_add]
      apply ih (j + 1) _ _ hv'
      intro i hi
      have := h (i + 1) (by omega)
      have e : j + (i + 1) = j + 1 + i := by omega
      simp only [scanFlags, e] at this
      exact this

/-- A register with a carry on a violator or after a violator is selected.

Consumer: `rank_progress`. -/
theorem selAt_carry (r p : Nat) (cells : Nat → Cell) (hc : (cells p).c ≠ .off)
    (h : violC (scanFlags cells p 0 false false).1 (cells p) = true ∨
      (scanFlags cells p 0 false false).2 = true) : SelAt r cells p := by
  unfold SelAt
  by_cases hp : p + 1 < r
  · rw [if_pos hp]; exact Or.inl ⟨hc, h⟩
  · rw [if_neg hp]; exact Or.inl ⟨hc, h⟩

/-- A front after a violator is selected.

Consumer: `rank_progress`. -/
theorem selAt_front (r p : Nat) (cells : Nat → Cell) (hx : (cells p).i = .x)
    (hc : (cells p).c = .off) (h : (scanFlags cells p 0 false false).2 = true) :
    SelAt r cells p := by
  unfold SelAt
  by_cases hp : p + 1 < r
  · rw [if_pos hp]; exact Or.inr (Or.inl ⟨hx, hc, h⟩)
  · rw [if_neg hp]; exact Or.inr (Or.inl ⟨hx, hc, h⟩)

/-- An inherited carry is selected.

Consumer: `rank_progress`. -/
theorem selAt_inh (r p : Nat) (cells : Nat → Cell) (h : (cells p).c = .inh) :
    SelAt r cells p := by
  unfold SelAt
  by_cases hp : p + 1 < r
  · rw [if_pos hp]; exact Or.inr (Or.inr (Or.inr h))
  · rw [if_neg hp]; exact Or.inr (Or.inr (Or.inr h))

/-- A pending input with an obstacle before it and an empty or settled next register is selected.

Consumer: `rank_progress`. -/
theorem selAt_pending (r p : Nat) (cells : Nat → Cell)
    (hP : (cells p).i.isP = true) (hc : (cells p).c = .off)
    (hob : (scanFlags cells p 0 false false).1 = true)
    (hnext : p + 1 < r →
      cells (p + 1) = { i := .e, c := .off } ∨
        ((cells (p + 1)).i.isS = true ∧ (cells (p + 1)).c = .off)) :
    SelAt r cells p := by
  unfold SelAt
  by_cases hp : p + 1 < r
  · rw [if_pos hp]; exact Or.inr (Or.inr (Or.inl ⟨hP, hc, hob, hnext hp⟩))
  · rw [if_neg hp]; exact Or.inr (Or.inr (Or.inl ⟨hP, hc, hob⟩))

/-- With a violator some register is selected.

Consumer: `rank_progress`. -/
theorem select_edge (r : Nat) (cells : Nat → Cell)
    (hv : ∃ i, i < r ∧ violC (scanFlags cells i 0 false false).1 (cells i) = true) :
    ∃ p, p < r ∧ SelAt r cells p := by
  obtain ⟨i, hi, hviol, hmax⟩ := exists_max r _ hv
  have hflag := scanFlags_succ_right cells i 0 false false
  simp only [Nat.zero_add] at hflag
  have hvb : (scanFlags cells (i + 1) 0 false false).2 = true := by
    rw [hflag]; simp [nvb, hviol]
  rcases hxc : cells i with ⟨xi, xc⟩
  have hviol' : violC (scanFlags cells i 0 false false).1 ⟨xi, xc⟩ = true := by
    rw [← hxc]; exact hviol
  have hxP : xi.isP = true := by
    cases xi <;> simp [violC, Inp.isP] at hviol' ⊢
  by_cases hcar : xc = .off
  · subst hcar
    have hobi : (scanFlags cells i 0 false false).1 = true := by
      cases xi <;> simp [violC, Inp.isP] at hviol' ⊢ <;> exact hviol'
    have hob1 : (scanFlags cells (i + 1) 0 false false).1 = true := by
      rw [hflag]; simp [nob, hobi]
    by_cases hlast : i + 1 < r
    · rcases hy : cells (i + 1) with ⟨yi, yc⟩
      by_cases hyc : yc = .off
      · subst hyc
        cases yi with
        | e =>
            refine ⟨i, hi, selAt_pending r i cells (by rw [hxc]; exact hxP) (by rw [hxc]) hobi ?_⟩
            intro _; rw [hy]; exact Or.inl rfl
        | sn =>
            refine ⟨i, hi, selAt_pending r i cells (by rw [hxc]; exact hxP) (by rw [hxc]) hobi ?_⟩
            intro _; rw [hy]; exact Or.inr ⟨rfl, rfl⟩
        | st =>
            refine ⟨i, hi, selAt_pending r i cells (by rw [hxc]; exact hxP) (by rw [hxc]) hobi ?_⟩
            intro _; rw [hy]; exact Or.inr ⟨rfl, rfl⟩
        | x =>
            exact ⟨i + 1, hlast, selAt_front r (i + 1) cells (by rw [hy]) (by rw [hy]) hvb⟩
        | pt =>
            exfalso
            apply hmax (i + 1) (by omega) hlast
            rw [hob1, hy]; rfl
        | pn =>
            exfalso
            apply hmax (i + 1) (by omega) hlast
            rw [hob1, hy]; rfl
      · exact ⟨i + 1, hlast, selAt_carry r (i + 1) cells (by rw [hy]; exact hyc) (Or.inr hvb)⟩
    · exact ⟨i, hi, selAt_pending r i cells (by rw [hxc]; exact hxP) (by rw [hxc]) hobi
        (fun h => absurd h hlast)⟩
  · exact ⟨i, hi, selAt_carry r i cells (by rw [hxc]; exact hcar) (Or.inl hviol)⟩

/-- Off rank zero some window edge strictly lowers the rank.

Consumer: `topClockMarkedDebtPhase_holds`. -/
theorem rank_progress (r : Nat) (hr : 2 ≤ r) (cells : Nat → Cell)
    (hpos : 0 < rank r cells) :
    ∃ p, p < r ∧ rank r (edgeStep r cells p) + 1 ≤ rank r cells := by
  by_cases hv : ∃ i, i < r ∧
      violC (scanFlags cells i 0 false false).1 (cells i) = true
  · obtain ⟨p, hp, hsel⟩ := select_edge r cells hv
    exact ⟨p, hp, edge_lt r p hp cells hsel⟩
  · by_cases hinh : ∃ j, j < r ∧ (cells j).c = .inh
    · obtain ⟨j, hj, hc⟩ := hinh
      exact ⟨j, hj, edge_lt r j hj cells (selAt_inh r j cells hc)⟩
    · exfalso
      have hzero : rank r cells = 0 := by
        unfold rank
        apply scan_zero_clean r cells r 0 false false rfl
        intro i hi
        refine ⟨?_, ?_⟩
        · cases h : violC (scanFlags cells i 0 false false).1 (cells (0 + i))
          · rfl
          · exact absurd ⟨i, hi, by simpa using h⟩ hv
        · intro h
          exact hinh ⟨0 + i, by omega, h⟩
      omega

end MarkedCells
end L3

#print axioms L3.MarkedCells.rank_progress
