import Leader.L4.WindowScopedFailure
import Leader.L4.WindowScopedOneEdge
import Leader.L4.WindowScopedModerateRestart

namespace L4.WindowScopedSealedMean
open WindowScopedRace

/-- The single sealed-sector deletion clock for all three geometric
regimes of the G6/G7 windows. The target is the actual scoped router's
first exit: a selected retirement or certified native death. -/
theorem mean {p c n : Nat} {initial : Config p c n} {group cert : List (Fin n)}
    {v : Fin n} {a b : Nat} (C : Context initial group cert v a b)
    (z : Cursor p c n) (hz : C.Certified z) :
    IIDExpectedHittingTimeAtMost (cursorNext group cert) Cursor.exit z
      (2560*n*((a+1)+(b+1))) := by
  by_cases hb : b=0
  · subst b
    apply TripleRenewal.expected_mono (WindowScopedOneEdge.mean C z hz)
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
  · by_cases hA : 2*(b+1)<a+1
    · apply TripleRenewal.expected_mono (WindowScopedFailure.scoped_long_mean C hA z hz)
      have h : 256*(10*n*((a+1)+(b+1)))=(256*10)*n*((a+1)+(b+1)) := by ac_rfl
      rw [h]
      exact Nat.le_refl _
    · apply TripleRenewal.expected_mono (WindowScopedModerateRestart.mean C (by omega) (by omega) z hz)
      have hm : 5*(a+1)+4*(b+1)≤40*((a+1)+(b+1)) := by omega
      have hh := Nat.mul_le_mul_left (64*n) hm
      calc
        _ = (64*n)*(5*(a+1)+4*(b+1)) := (Nat.mul_assoc ..).symm
        _ ≤ (64*n)*(40*((a+1)+(b+1))) := hh
        _ = _ := by
          calc
            _ = (64*40)*n*((a+1)+(b+1)) := by ac_rfl
            _ = _ := rfl

/-- Paper-compatible rounded coefficient for the same cursor. -/
theorem mean_4096 {p c n : Nat} {initial : Config p c n} {group cert : List (Fin n)}
    {v : Fin n} {a b : Nat} (C : Context initial group cert v a b)
    (z : Cursor p c n) (hz : C.Certified z) :
    IIDExpectedHittingTimeAtMost (cursorNext group cert) Cursor.exit z
      (4096*n*((a+1)+(b+1))) :=
  TripleRenewal.expected_mono (mean C z hz)
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide)))

end L4.WindowScopedSealedMean

#print axioms L4.WindowScopedSealedMean.mean

#print axioms L4.WindowScopedSealedMean.mean_4096
