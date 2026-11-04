import Leader.L3.Top.SettledWorkTerm
import Leader.L3.Top.MarkedRank

/-!
# Q7 (P.6): the barrier is kept along every abstract step

The marked-debt rank is nonincreasing (`rank_step_le`).  A window with the moving barrier and
no inherited carry has rank zero, and rank zero is the barrier.  Hence the barrier is kept by
every abstract step, with settled inputs present.

Consumer: `Leader/L3/Top/SettledWorkTrace.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The scan of a window with the barrier and no inherited carry is zero.

Consumer: `rank_zero_of_barrier`. -/
theorem scan_zero_of_barrier (r : Nat) (cells : Nat → Cell) (hbar : Barrier r cells)
    (hni : NoInh r cells) :
    ∀ k j ob, j + k ≤ r → (ob = true ↔ ∃ b, b < j ∧ obC (cells b) = true) →
      scan r cells k j ob false = 0 := by
  intro k
  induction k with
  | zero => intro j ob _ _; rfl
  | succ k ih =>
      intro j ob hjk hob
      have hjr : j < r := by omega
      have hviol : violC ob (cells j) = false := by
        cases hP : (cells j).i.isP
        · simp [violC, hP]
        · cases hc : decide ((cells j).c ≠ .off)
          · cases hob' : ob
            · simp [violC, hP, hc]
            · exfalso
              obtain ⟨b, hb, hbo⟩ := hob.1 hob'
              have := hbar j b hjr (by omega) hP hbo
              omega
          · exfalso
            have hne : (cells j).c ≠ .off := by simpa using hc
            have hobj : obC (cells j) = true := by simp [obC, hne]
            have := hbar j j hjr hjr hP hobj
            omega
      have hwt : wt r j ob false (cells j) = 0 := by
        have hinh := hni j hjr
        simp [wt, hviol, hinh]
      simp only [scan]
      rw [hwt, Nat.zero_add]
      have hflag : nvb ob false (cells j) = false := by simp [nvb, hviol]
      rw [hflag]
      refine ih (j + 1) (nob ob (cells j)) (by omega) ?_
      constructor
      · intro h
        simp only [nob, Bool.or_eq_true] at h
        rcases h with h | h
        · obtain ⟨b, hb, hbo⟩ := hob.1 h
          exact ⟨b, by omega, hbo⟩
        · exact ⟨j, by omega, h⟩
      · rintro ⟨b, hb, hbo⟩
        simp only [nob, Bool.or_eq_true]
        by_cases hbj : b = j
        · subst hbj; exact Or.inr hbo
        · exact Or.inl (hob.2 ⟨b, by omega, hbo⟩)

/-- Barrier and no inherited carry give rank zero.

Consumer: `barrier_step`. -/
theorem rank_zero_of_barrier (r : Nat) (cells : Nat → Cell) (hbar : Barrier r cells)
    (hni : NoInh r cells) : rank r cells = 0 := by
  unfold rank
  exact scan_zero_of_barrier r cells hbar hni r 0 false (by omega) (by simp)

/-- **The barrier is kept by every abstract step** (no inherited carry).

Consumer: `Leader/L3/Top/SettledWorkTrace.lean`. -/
theorem barrier_step (r : Nat) (hr : 2 ≤ r) (cells cells' : Nat → Cell)
    (hbar : Barrier r cells) (hni : NoInh r cells) (h : Step r cells cells') :
    Barrier r cells' :=
  rank_zero_barrier r cells' (Nat.le_zero.1
    (by have := rank_step_le r hr cells cells' h
        rw [rank_zero_of_barrier r cells hbar hni] at this
        exact this))

end MarkedCells
end L3

#print axioms L3.MarkedCells.barrier_step
