import Leader.L3.Top.PinnedRaceRows
import Leader.L3.Top.PreparationPhase

/-!
# Q7 (P.12 race): the abstract cells of a misplaced-tail cut

A misplaced-tail cut has the cells `E/P` (no carry) before the tail, the settled tail `st` at
`h`, settled non-tails `sn` after it, and no carry.  Such a window has marked-debt rank zero
(`misAt_rank_zero`); a front-free pair of `E/P` registers stays `E/P` under one edge
(`pair_ep_off`).

Consumer: `Leader/L3/Top/PinnedRaceStep.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The scan of a block splits.

Consumer: `rank_zero_of_prefix`. -/
theorem scan_split_add (r : Nat) (cells : Nat → Cell) :
    ∀ a k j ob vb, scan r cells (a + k) j ob vb =
      scan r cells a j ob vb + scan r cells k (j + a)
        (scanFlags cells a j ob vb).1 (scanFlags cells a j ob vb).2 := by
  intro a
  induction a with
  | zero => intro k j ob vb; simp [scan, scanFlags]
  | succ a ih =>
    intro k j ob vb
    have e : a + 1 + k = (a + k) + 1 := by omega
    rw [e]
    simp only [scan, scanFlags]
    rw [ih k (j + 1) (nob ob (cells j)) (nvb ob vb (cells j))]
    have e2 : j + 1 + a = j + (a + 1) := by omega
    rw [e2]
    omega

/-- `E/P` registers without carry give zero weight and keep the flags clear.

Consumer: `rank_zero_of_prefix`. -/
theorem scan_prefix_zero (r : Nat) (cells : Nat → Cell) :
    ∀ k j, (∀ i, j ≤ i → i < j + k → EP (cells i) ∧ (cells i).c = .off) →
      scan r cells k j false false = 0 ∧ scanFlags cells k j false false = (false, false) := by
  intro k
  induction k with
  | zero => intro j _; simp [scan, scanFlags]
  | succ k ih =>
    intro j h
    have hj := h j (Nat.le_refl _) (by omega)
    have hflags : nob false (cells j) = false ∧ nvb false false (cells j) = false := by
      obtain ⟨hep, hc⟩ := hj
      rcases hcl : cells j with ⟨ci, cc⟩
      rw [hcl] at hep hc
      simp only at hc
      subst hc
      unfold EP at hep
      simp only at hep
      cases ci <;> simp_all [nob, nvb, obC, violC, Inp.isP, Inp.isS]
    have hw : wt r j false false (cells j) = 0 := by
      obtain ⟨hep, hc⟩ := hj
      rcases hcl : cells j with ⟨ci, cc⟩
      rw [hcl] at hep hc
      simp only at hc
      subst hc
      unfold EP at hep
      simp only at hep
      cases ci <;> simp_all [wt, gateW, violC, Inp.isP, Inp.isS]
    simp only [scan, scanFlags]
    rw [hflags.1, hflags.2, hw]
    have := ih (j + 1) (fun i hi1 hi2 => h i (by omega) (by omega))
    refine ⟨by omega, this.2⟩

/-- Settled registers without carry give zero weight when no violator has been seen.

Consumer: `rank_zero_of_prefix`. -/
theorem scan_suffix_zero (r : Nat) (cells : Nat → Cell) :
    ∀ k j ob, (∀ i, j ≤ i → i < j + k → (cells i).i.isS = true ∧ (cells i).c = .off) →
      scan r cells k j ob false = 0 := by
  intro k
  induction k with
  | zero => intro j ob _; simp [scan]
  | succ k ih =>
    intro j ob h
    have hj := h j (Nat.le_refl _) (by omega)
    have hw : wt r j ob false (cells j) = 0 := by
      obtain ⟨hs, hc⟩ := hj
      rcases hcl : cells j with ⟨ci, cc⟩
      rw [hcl] at hs hc
      simp only at hs hc
      subst hc
      cases ci <;> simp_all [wt, gateW, violC, Inp.isP, Inp.isS]
    have hv : nvb ob false (cells j) = false := by
      obtain ⟨hs, hc⟩ := hj
      rcases hcl : cells j with ⟨ci, cc⟩
      rw [hcl] at hs hc
      simp only at hs hc
      subst hc
      cases ci <;> simp_all [nvb, violC, Inp.isP, Inp.isS]
    simp only [scan]
    rw [hw, hv, ih (j + 1) _ (fun i hi1 hi2 => h i (by omega) (by omega))]

/-- **A window of `E/P` registers then settled registers, without carry, has rank zero.**

Consumer: `misAt_rank_zero`. -/
theorem rank_zero_of_prefix (r b : Nat) (cells : Nat → Cell) (hb : b ≤ r)
    (hL : ∀ j, j < b → EP (cells j) ∧ (cells j).c = .off)
    (hR : ∀ j, b ≤ j → j < r → (cells j).i.isS = true ∧ (cells j).c = .off) :
    rank r cells = 0 := by
  unfold rank
  have hs := scan_split_add r cells b (r - b) 0 false false
  have e : b + (r - b) = r := by omega
  rw [e] at hs
  rw [hs]
  have h1 := scan_prefix_zero r cells b 0 (fun i _ hi => hL i (by omega))
  rw [h1.2]
  simp only
  rw [h1.1, scan_suffix_zero r cells (r - b) (0 + b) false (fun i hi1 hi2 =>
    hR i (by omega) (by omega))]

/-- Two `E/P` registers without carry stay `E/P` without carry under one edge.

Consumer: `Leader/L3/Top/PinnedRaceStep.lean`. -/
theorem pair_ep_off (b : Bool) (x y : Cell) (hx : EP x) (hxc : x.c = .off) (hy : EP y)
    (hyc : y.c = .off) :
    EP (pair b false x y).1 ∧ (pair b false x y).1.c = .off ∧
    EP (pair b false x y).2 ∧ (pair b false x y).2.c = .off := by
  rcases x with ⟨xi, xc⟩
  rcases y with ⟨yi, yc⟩
  simp only at hxc hyc
  subst hxc hyc
  unfold EP at hx hy
  simp only at hx hy
  cases xi <;> cases yi <;> cases b <;>
    simp_all (config := { decide := true }) [EP, pair, inSlots, carries, Inp.isP, Inp.isS]

end MarkedCells
end L3

#print axioms L3.MarkedCells.rank_zero_of_prefix
#print axioms L3.MarkedCells.pair_ep_off
