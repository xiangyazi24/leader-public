import Leader.L3.Top.OldMarkProgress

/-!
# Q7: the rightmost marked violator selects an edge

Consumer: `Leader/L3/Top/OldMarkStep.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- A register with a live carry after the flags is selected.

Consumer: `select_old`. -/
theorem selOAt_carry (r p : Nat) (cells : Nat → Cell) (o : Nat → Bool)
    (hc : (cells p).c ≠ .off)
    (h : violC (scanFlags (markCells cells o) p 0 false false).1 (cells p) = true ∨
      (scanFlags (markCells cells o) p 0 false false).2 = true) : SelOAt r cells o p := by
  unfold SelOAt
  by_cases hp : p + 1 < r
  · rw [if_pos hp]; exact Or.inl ⟨hc, h⟩
  · rw [if_neg hp]; exact Or.inl ⟨hc, h⟩

/-- A front after a violator is selected.

Consumer: `select_old`. -/
theorem selOAt_front (r p : Nat) (cells : Nat → Cell) (o : Nat → Bool)
    (hx : (cells p).i = .x) (hc : (cells p).c = .off)
    (h : (scanFlags (markCells cells o) p 0 false false).2 = true) : SelOAt r cells o p := by
  unfold SelOAt
  by_cases hp : p + 1 < r
  · rw [if_pos hp]; exact Or.inr (Or.inl ⟨hx, hc, h⟩)
  · rw [if_neg hp]; exact Or.inr (Or.inl ⟨hx, hc, h⟩)

/-- An inherited carry is selected.

Consumer: `rank_progress_old`. -/
theorem selOAt_inh (r p : Nat) (cells : Nat → Cell) (o : Nat → Bool)
    (h : (cells p).c = .inh) : SelOAt r cells o p := by
  unfold SelOAt
  by_cases hp : p + 1 < r
  · rw [if_pos hp]; exact Or.inr (Or.inr (Or.inr h))
  · rw [if_neg hp]; exact Or.inr (Or.inr (Or.inr h))

/-- A pending input with an obstacle or a mark, and a free or settled next register, is
selected.

Consumer: `select_old`. -/
theorem selOAt_pend (r p : Nat) (cells : Nat → Cell) (o : Nat → Bool)
    (hP : (cells p).i.isP = true) (hc : (cells p).c = .off)
    (hob : (scanFlags (markCells cells o) p 0 false false).1 = true ∨ o p = true)
    (hnext : p + 1 < r →
      cells (p + 1) = { i := .e, c := .off } ∨
        ((cells (p + 1)).i.isS = true ∧ (cells (p + 1)).c = .off)) :
    SelOAt r cells o p := by
  unfold SelOAt
  by_cases hp : p + 1 < r
  · rw [if_pos hp]; exact Or.inr (Or.inr (Or.inl ⟨hP, hc, hob, hnext hp⟩))
  · rw [if_neg hp]; exact Or.inr (Or.inr (Or.inl ⟨hP, hc, hob⟩))

/-- With a marked violator some register is selected.

Consumer: `rank_progress_old`. -/
theorem select_old (r : Nat) (cells : Nat → Cell) (o : Nat → Bool)
    (hv : ∃ i, i < r ∧
      violC (scanFlags (markCells cells o) i 0 false false).1 (markCells cells o i) = true) :
    ∃ p, p < r ∧ SelOAt r cells o p := by
  obtain ⟨i, hi, hviol, hmax⟩ := exists_max r _ hv
  have hflag := scanFlags_succ_right (markCells cells o) i 0 false false
  simp only [Nat.zero_add] at hflag
  have hvb : (scanFlags (markCells cells o) (i + 1) 0 false false).2 = true := by
    rw [hflag]; simp [nvb, hviol]
  rcases hxc : cells i with ⟨xi, xc⟩
  have hviol' : violC (scanFlags (markCells cells o) i 0 false false).1
      (mk ⟨xi, xc⟩ (o i)) = true := by
    have : markCells cells o i = mk ⟨xi, xc⟩ (o i) := by simp [markCells, hxc]
    rw [← this]; exact hviol
  have hxP : xi.isP = true := by
    cases hoi : o i <;> cases xi <;> simp [violC, mk, hoi, Inp.isP] at hviol' ⊢
  -- the obstacle flag after register `i`
  have hob1 : (scanFlags (markCells cells o) (i + 1) 0 false false).1 = true := by
    rw [hflag]
    cases hoi : o i
    · -- no mark: the violator has an obstacle before it, or a carry
      cases xi <;> simp [violC, mk, hoi, Inp.isP] at hviol' hxP
      all_goals first
        | (simp [nob, obC, markCells, hxc, hoi, hviol']; done)
        | (cases xc <;> simp_all [nob, obC, markCells, mk])
    · simp [nob, obC, markCells, hxc, hoi, mk]
  by_cases hcar : xc = .off
  · subst hcar
    have hob_or : (scanFlags (markCells cells o) i 0 false false).1 = true ∨ o i = true := by
      cases hoi : o i
      · left
        cases xi <;> simp [violC, mk, hoi, Inp.isP] at hviol' hxP ⊢
        all_goals exact hviol'
      · right; rfl
    by_cases hlast : i + 1 < r
    · rcases hy : cells (i + 1) with ⟨yi, yc⟩
      by_cases hyc : yc = .off
      · subst hyc
        cases yi with
        | e =>
            exact ⟨i, hi, selOAt_pend r i cells o (by rw [hxc]; exact hxP) (by rw [hxc])
              hob_or (fun _ => by rw [hy]; exact Or.inl rfl)⟩
        | sn =>
            exact ⟨i, hi, selOAt_pend r i cells o (by rw [hxc]; exact hxP) (by rw [hxc])
              hob_or (fun _ => by rw [hy]; exact Or.inr ⟨rfl, rfl⟩)⟩
        | st =>
            exact ⟨i, hi, selOAt_pend r i cells o (by rw [hxc]; exact hxP) (by rw [hxc])
              hob_or (fun _ => by rw [hy]; exact Or.inr ⟨rfl, rfl⟩)⟩
        | x =>
            exact ⟨i + 1, hlast, selOAt_front r (i + 1) cells o (by rw [hy]) (by rw [hy]) hvb⟩
        | pt =>
            exfalso
            apply hmax (i + 1) (by omega) hlast
            have : markCells cells o (i + 1) = mk ⟨Inp.pt, Car.off⟩ (o (i + 1)) := by
              simp [markCells, hy]
            rw [this, hob1]
            cases o (i + 1) <;> simp [violC, mk, Inp.isP]
        | pn =>
            exfalso
            apply hmax (i + 1) (by omega) hlast
            have : markCells cells o (i + 1) = mk ⟨Inp.pn, Car.off⟩ (o (i + 1)) := by
              simp [markCells, hy]
            rw [this, hob1]
            cases o (i + 1) <;> simp [violC, mk, Inp.isP]
      · exact ⟨i + 1, hlast, selOAt_carry r (i + 1) cells o (by rw [hy]; exact hyc) (Or.inr hvb)⟩
    · exact ⟨i, hi, selOAt_pend r i cells o (by rw [hxc]; exact hxP) (by rw [hxc])
        hob_or (fun h => absurd h hlast)⟩
  · refine ⟨i, hi, selOAt_carry r i cells o (by rw [hxc]; exact hcar) (Or.inl ?_)⟩
    rw [hxc]
    cases xi <;> simp [violC, Inp.isP] at hxP ⊢
    all_goals first | exact hcar | simp [hcar]

/-- Off marked-rank zero some window edge strictly lowers the marked rank.

Consumer: `rank_old_step`. -/
theorem rank_progress_old (r : Nat) (hr : 2 ≤ r) (cells : Nat → Cell) (o : Nat → Bool)
    (ho : ∀ j, j < r → o j = true → (cells j).i.isP = true)
    (hf : ∀ j, j < r → (cells j).c = .fresh → (cells j).i = .e)
    (hpos : 0 < rank r (markCells cells o)) :
    ∃ p, p < r ∧ rank r (markCells (edgeStep r cells p) (flagsAt r cells o p)) + 1 ≤
      rank r (markCells cells o) := by
  by_cases hv : ∃ i, i < r ∧
      violC (scanFlags (markCells cells o) i 0 false false).1 (markCells cells o i) = true
  · obtain ⟨p, hp, hsel⟩ := select_old r cells o hv
    exact ⟨p, hp, rank_edge_old_lt r p hp cells o ho hf hsel⟩
  · by_cases hinh : ∃ j, j < r ∧ (cells j).c = .inh
    · obtain ⟨j, hj, hc⟩ := hinh
      exact ⟨j, hj, rank_edge_old_lt r j hj cells o ho hf (selOAt_inh r j cells o hc)⟩
    · exfalso
      have hzero : rank r (markCells cells o) = 0 := by
        unfold rank
        apply scan_zero_clean r (markCells cells o) r 0 false false rfl
        intro i hi
        refine ⟨?_, ?_⟩
        · cases h : violC (scanFlags (markCells cells o) i 0 false false).1
              (markCells cells o (0 + i))
          · rfl
          · exact absurd ⟨i, hi, by simpa using h⟩ hv
        · intro h
          have hmk : (markCells cells o (0 + i)).c = .inh := h
          by_cases hoi : o (0 + i) = true
          · -- a mark is a violator
            apply hv
            refine ⟨0 + i, by omega, ?_⟩
            have hP := ho (0 + i) (by omega) hoi
            simp only [markCells, mk, hoi, if_true]
            simp only [violC]
            rw [hP]
            simp
          · apply hinh
            refine ⟨0 + i, by omega, ?_⟩
            have hoi' : o (0 + i) = false := by simpa using hoi
            simp only [markCells, mk, hoi', Bool.false_eq_true, if_false] at hmk
            exact hmk
      omega

end MarkedCells
end L3

#print axioms L3.MarkedCells.select_old
#print axioms L3.MarkedCells.rank_progress_old
