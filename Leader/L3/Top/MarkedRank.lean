import Leader.L3.Top.MarkedCells

/-!
# Q7: the rank never rises on a window edge

Consumer: `Leader/L3/Top/MarkedDebtRows.lean` (nonincrease row of
`TopMarkedDebtRows`).
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- Patch of one cell with a suffix of `m` further cells.

Consumer: `topClockMarkedDebtPhase_holds`. -/
theorem patch_one (r p : Nat) (hp : p < r) (cells cells' : Nat → Cell)
    (hout : ∀ i, i ≠ p → cells' i = cells i)
    (hloc : ∀ ob vb, scanFlags cells p 0 false false = (ob, vb) →
      (vb = true → ob = true) →
      wt r p ob vb (cells' p) ≤ wt r p ob vb (cells p) ∧
      (nob ob (cells' p) = true → nob ob (cells p) = true) ∧
      (nvb ob vb (cells' p) = true → nvb ob vb (cells p) = true)) :
    rank r cells' ≤ rank r cells := by
  obtain ⟨m, hm⟩ : ∃ m, r = p + (m + 1) := ⟨r - p - 1, by omega⟩
  have hpre := scan_congr r cells cells' p 0 false false
    (fun i _ hi => hout i (by omega))
  have hvalid := scanFlags_valid cells p 0 false false (fun h => by simp at h)
  have hrank : ∀ cs : Nat → Cell, rank r cs =
      scan r cs p 0 false false +
        scan r cs (m + 1) p (scanFlags cs p 0 false false).1
          (scanFlags cs p 0 false false).2 := by
    intro cs
    unfold rank
    have h := scan_add r cs p (m + 1) 0 false false
    rw [← hm, Nat.zero_add] at h
    exact h
  rw [hrank cells', hrank cells, hpre.1, hpre.2]
  generalize hf : scanFlags cells p 0 false false = f at *
  obtain ⟨ob, vb⟩ := f
  have hloc' := hloc ob vb rfl hvalid
  have hsuf := scan_congr r cells cells' m (p + 1) (nob ob (cells' p))
    (nvb ob vb (cells' p))
    (fun i h1 h2 => hout i (by omega))
  have hmono := scan_mono r cells m (p + 1)
    (nob ob (cells' p)) (nob ob (cells p))
    (nvb ob vb (cells' p)) (nvb ob vb (cells p))
    hloc'.2.1 hloc'.2.2
  have e2 : ∀ cs : Nat → Cell, scan r cs (m + 1) p ob vb =
      wt r p ob vb (cs p) +
        scan r cs m (p + 1) (nob ob (cs p)) (nvb ob vb (cs p)) := by
    intro cs
    rfl
  rw [e2 cells', e2 cells, hsuf.1]
  have := hloc'.1
  omega

/-- Patch of the last cell: only the weight matters.

Consumer: `topClockMarkedDebtPhase_holds`. -/
theorem patch_last (r p : Nat) (hp : p + 1 = r) (cells cells' : Nat → Cell)
    (hout : ∀ i, i ≠ p → cells' i = cells i)
    (hloc : ∀ ob vb, scanFlags cells p 0 false false = (ob, vb) →
      (vb = true → ob = true) →
      wt r p ob vb (cells' p) ≤ wt r p ob vb (cells p)) :
    rank r cells' ≤ rank r cells := by
  have hpre := scan_congr r cells cells' p 0 false false
    (fun i _ hi => hout i (by omega))
  have hvalid := scanFlags_valid cells p 0 false false (fun h => by simp at h)
  have hrank : ∀ cs : Nat → Cell, rank r cs =
      scan r cs p 0 false false +
        scan r cs 1 p (scanFlags cs p 0 false false).1
          (scanFlags cs p 0 false false).2 := by
    intro cs
    unfold rank
    have h := scan_add r cs p 1 0 false false
    rw [← hp, Nat.zero_add] at h
    rw [hp] at h
    exact h
  rw [hrank cells', hrank cells, hpre.1, hpre.2]
  generalize hf : scanFlags cells p 0 false false = f at *
  obtain ⟨ob, vb⟩ := f
  have hloc' := hloc ob vb rfl hvalid
  have e2 : ∀ cs : Nat → Cell, scan r cs 1 p ob vb = wt r p ob vb (cs p) := by
    intro cs
    simp [scan]
  rw [e2 cells', e2 cells]
  omega

/-- Local weight inequality of the terminal edge.

Consumer: `rank_step_le`. -/
theorem term_local (r p : Nat) (hp : p + 1 = r) (x y : Cell) (ob vb : Bool)
    (hv : vb = true → ob = true) :
    wt r p ob vb (pair false true x y).1 ≤ wt r p ob vb x := by
  rcases x with ⟨xi, xc⟩
  rcases y with ⟨yi, yc⟩
  cases xi <;> cases xc <;> cases ob <;> cases vb <;>
    simp (config := { decide := true })
      [pair, inSlots, carries, wt, gateW, violC] at hv ⊢ <;> omega

/-- Local inequality of the port host cleanup.

Consumer: `rank_step_le`. -/
theorem clean_local (r : Nat) (hr : 0 < r) (c : Cell) :
    wt r 0 false false (portClean c) ≤ wt r 0 false false c ∧
    (nob false (portClean c) = true → nob false c = true) ∧
    (nvb false false (portClean c) = true → nvb false false c = true) := by
  rcases c with ⟨ci, cc⟩
  cases ci <;> cases cc <;>
    simp (config := { decide := true })
      [portClean, wt, gateW, violC, nob, nvb, obC, Inp.isP, Inp.isS]

/-- Local inequality of the port acceptance.

Consumer: `rank_step_le`. -/
theorem accept_local (r : Nat) (hr : 0 < r) (t : Bool) (c : Cell) :
    wt r 0 false false (portAccept t c) ≤ wt r 0 false false c ∧
    (nob false (portAccept t c) = true → nob false c = true) ∧
    (nvb false false (portAccept t c) = true → nvb false false c = true) := by
  rcases c with ⟨ci, cc⟩
  cases t <;> cases ci <;> cases cc <;>
    simp (config := { decide := true })
      [portAccept, wt, gateW, violC, nob, nvb, obC, Inp.isP, Inp.isS]

/-- No window edge raises the rank.

Consumer: `topClockMarkedDebtPhase_holds`. -/
theorem rank_step_le (r : Nat) (hr : 2 ≤ r) (cells cells' : Nat → Cell)
    (h : Step r cells cells') : rank r cells' ≤ rank r cells := by
  cases h with
  | frame => exact Nat.le_refl _
  | edge p hp =>
      apply patch_two r p hp
      · intro i h1 h2
        simp [setTwo, h1, h2]
      · intro ob vb _ hv
        have := pair_local r p hp (decide (p = 0)) (cells p) (cells (p + 1)) ob vb hv
        simpa [setTwo] using this
  | term =>
      apply patch_last r (r - 1) (by omega)
      · intro i h1
        simp [setOne, h1]
      · intro ob vb _ hv
        have := term_local r (r - 1) (by omega) (cells (r - 1)) { i := .e, c := .off } ob vb hv
        simpa [setOne] using this
  | clean =>
      apply patch_one r 0 (by omega)
      · intro i h1
        simp [setOne, h1]
      · intro ob vb hf _
        have hf' : scanFlags cells 0 0 false false = (false, false) := rfl
        rw [hf'] at hf
        cases hf
        simpa [setOne] using clean_local r (by omega) (cells 0)
  | accept t =>
      apply patch_one r 0 (by omega)
      · intro i h1
        simp [setOne, h1]
      · intro ob vb hf _
        have hf' : scanFlags cells 0 0 false false = (false, false) := rfl
        rw [hf'] at hf
        cases hf
        simpa [setOne] using accept_local r (by omega) t (cells 0)

end MarkedCells
end L3

#print axioms L3.MarkedCells.rank_step_le
